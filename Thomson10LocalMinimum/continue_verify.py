#!/usr/bin/env python3
"""Continue one's own interrupted fresh build, without resetting its time budget."""
import hashlib
import json
import os
import re
import sys
import time
import uuid
from pathlib import Path
import verify as V

def main(relative):
    run = (V.ROOT / relative).resolve()
    output_root = (V.ROOT / '.verification-output').resolve()
    if run.parent != output_root:
        raise V.VerificationError('Select one direct child of .verification-output')
    summary_path = run/'summary.json'
    original = V.read_json(summary_path, 'interrupted summary')
    if original['status'] != 'failed':
        raise V.VerificationError('Only an interrupted failed run can be continued')
    manifest = V.read_json(V.ROOT/'source-manifest.json','source manifest')
    order = V.check_hashes(manifest)
    revisions, manifest_hash = V.check_pins(manifest)
    if original.get('lake_manifest_sha256') != manifest_hash:
        raise V.VerificationError('Dependency manifest changed since the interrupted run')
    if original.get('actual_dependency_revisions_checked') is not True:
        raise V.VerificationError('The interrupted run never checked actual dependency revisions')
    build = run/'build'
    if original['build_directory'] != V.relpath(build):
        raise V.VerificationError('Build-directory mismatch')
    records = original['commands'].copy()
    prefix = [c for c in records if c['name'].startswith('module-') and c['exit_code']==0 and not c['timed_out']]
    artifacts=[]
    for i,record in enumerate(prefix,1):
        module=order[i-1]
        if record['name'] != f'module-{i:03d}-{module}':
            raise V.VerificationError('Completed modules are not a contiguous dependency-ordered prefix')
        artifact=build/f'{module}.olean'
        log=V.ROOT/record['log']
        if not artifact.is_file() or not log.is_file() or not log.resolve().is_relative_to(run):
            raise V.VerificationError('A completed module artifact or log is missing')
        if 'return_code: 0' not in log.read_text(encoding='utf-8'):
            raise V.VerificationError('A completed module log does not record success')
        artifacts.append(dict(module=module,artifact_sha256=hashlib.sha256(artifact.read_bytes()).hexdigest()))
    if len(prefix) > len(order):
        raise V.VerificationError('The recorded module prefix is longer than the source order')
    previous_elapsed=float(original['elapsed_seconds'])
    remaining=V.TOTAL_TIMEOUT_SECONDS-previous_elapsed
    if remaining <= 0:
        raise V.VerificationError('The cumulative configured budget is exhausted')
    deadline=time.monotonic()+remaining
    V.write_summary(run/f'summary-interruption-{uuid.uuid4().hex[:8]}.json',original)
    summary=dict(original,status='running',continued_in_same_fresh_run=True,
        prefix_modules_retained=len(prefix),prefix_artifacts_at_continuation=artifacts,
        continuation_verifier_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),commands=records)
    try:
        lake=V.resolve_tool('LAKE_BIN','lake');lean=V.resolve_tool('LEAN_BIN','lean');git=V.resolve_tool('GIT_BIN','git')
        env=os.environ.copy();env.pop('LEAN_PATH',None)
        env.update(LEAN_NUM_THREADS='1',RAYON_NUM_THREADS='1',PYTHONIOENCODING='utf-8')
        config=int(env.get('GIT_CONFIG_COUNT','0'))
        for dep in revisions:
            checkout=(V.ROOT/'.lake/packages'/dep['name']).resolve()
            r=V.run_logged([git,'-c','safe.directory='+checkout.as_posix(),'-C',str(checkout),'rev-parse','HEAD'],
                'resume-revision-'+dep['name'],env,deadline,run,records)
            if r.returncode or r.stdout.strip()!=dep['revision']:
                raise V.VerificationError('Pinned dependency checkout changed')
            env[f'GIT_CONFIG_KEY_{config}']='safe.directory';env[f'GIT_CONFIG_VALUE_{config}']=checkout.as_posix();config+=1
        env['GIT_CONFIG_COUNT']=str(config)
        version=V.run_logged([lean,'--version'],'resume-lean-version',env,deadline,run,records)
        if version.returncode or not re.search(r'\bversion\s+4\.34\.1\b',version.stdout+version.stderr):
            raise V.VerificationError('Pinned Lean version changed')
        probe=V.run_logged([lake,'env',sys.executable,'-X','utf8','-c',"import os; print(os.environ.get('LEAN_PATH',''))"],
            'resume-lake-external-lean-path',env,deadline,run,records)
        lines=[s.strip() for s in probe.stdout.splitlines() if s.strip()]
        if probe.returncode or not lines:raise V.VerificationError('No dependency path')
        external=V.external_lean_path(lines[-1])
        if not external:raise V.VerificationError('Empty dependency path')
        env['LEAN_PATH']=os.pathsep.join([str(build),*external])
        def compile_source(source,output,label):
            r=V.run_logged([lean,'-j','1','-R',str(V.ROOT/'src'),'-o',str(output),str(source)],label,env,deadline,run,records)
            if r.returncode:raise V.VerificationError('Lean failed: '+label)
            return r.stdout+r.stderr
        print(f'Continuing the same fresh build after {len(prefix)}/{len(order)} modules',flush=True)
        for i,module in enumerate(order[len(prefix):],len(prefix)+1):
            compile_source(V.ROOT/'src'/f'{module}.lean',build/f'{module}.olean',f'module-{i:03d}-{module}')
            print(f'compiled {i}/{len(order)}: {module}',flush=True)
        controls=compile_source(V.ROOT/'src/WitnessControls.lean',build/'WitnessControls.olean','witness-controls')
        summary['witness_control_axioms']={t:V.verify_reported_target(t,controls) for t in [
            'Thomson10PublicWitness.original_node_0_check','Thomson10PublicWitness.damaged_node_0_check']}
        audit=compile_source(V.ROOT/'src/Audit.lean',build/'Audit.olean','main-audit')
        summary['main_theorem_axioms']={t:V.verify_reported_target(t,audit) for t in [
            'Thomson10Stability.certified_full_sphere_local_minimum','Thomson10Stability.certified_gauged_slice_local_minimum']}
        missing=('unknown identifier','unknown constant','unknown namespace','invalid import',
            'could not find module','failed to load','no such file')
        for filename,label,marker in [('False.lean','negative-false-proposition','0 = 1'),
            ('DamagedMatrixWitness.lean','negative-damaged-matrix-witness','Thomson10PublicWitness.damaged_node_0_check')]:
            r=V.run_logged([lean,'-j','1',str(V.ROOT/'negative-controls'/filename)],label,env,deadline,run,records)
            text=r.stdout+r.stderr;lower=text.lower()
            if r.returncode==0 or marker not in text or any(m in lower for m in missing) or not ('decide' in lower or 'unsolved goals' in lower):
                raise V.VerificationError('Negative control failed at an unintended location: '+filename)
            if filename=='DamagedMatrixWitness.lean' and '= true' not in text:
                raise V.VerificationError('Damaged control did not reach its false proposition')
        summary['negative_controls']={'false_proposition':'rejected as expected',
            'damaged_matrix_witness':'rejected at the false checker proposition as expected'}
        interrupted=[c for c in records if c['timed_out'] or c['name'].startswith('module-') and c['exit_code']!=0]
        summary['interrupted_attempts']=original.get('interrupted_attempts',[])+interrupted
        summary['commands']=[c for c in records if c not in interrupted]
        summary['status']='passed';summary.pop('error',None)
        summary['elapsed_seconds']=round(time.monotonic()-deadline+V.TOTAL_TIMEOUT_SECONDS,3)
        V.write_summary(summary_path,summary)
        print('PASS: all 183 original modules from the same fresh build, 4 axiom reports and both negative controls',flush=True)
        return 0
    except (V.VerificationError,OSError) as exc:
        summary.update(status='failed',error=str(exc),elapsed_seconds=round(time.monotonic()-deadline+V.TOTAL_TIMEOUT_SECONDS,3))
        V.write_summary(summary_path,summary)
        print('FAIL: '+str(exc),file=sys.stderr)
        return 1

if __name__=='__main__':
    if len(sys.argv)!=2:raise SystemExit('Usage: python continue_verify.py .verification-output/RUN_NAME')
    try:raise SystemExit(main(sys.argv[1]))
    except (V.VerificationError,OSError,KeyError) as exc:raise SystemExit('FAIL: '+str(exc))
