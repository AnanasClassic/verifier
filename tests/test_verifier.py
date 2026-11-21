import importlib.util
import json
from pathlib import Path
import tempfile
import sys
import unittest

ROOT = Path(__file__).resolve().parents[1]
# verifier.py imports verdicts from scripts/, as when it runs there; the test then also runs alone.
sys.path.insert(0, str(ROOT / 'scripts'))
spec = importlib.util.spec_from_file_location('verifier', ROOT / 'scripts/verifier.py')
v = importlib.util.module_from_spec(spec); spec.loader.exec_module(v)


class RequestTests(unittest.TestCase):
    def request(self):
        return {'repo_url': 'https://github.com/chafreaky/wht-power-saving-lean',
                'commit': '837dc3130adc79f7b7ab4ddd56c15576bbd766b0',
                'challenge_file': 'challenges/dft/UniformFourier233.lean',
                'theorem_names': 'OAI.PowerSaving.transform_mainY,OAI.PowerSaving.convolution_mainY',
                'lean_toolchain': 'leanprover/lean4:v4.34.1'}

    def test_reviewed_request(self):
        profile, names = v.validate_request(self.request())
        self.assertEqual(len(names), 2)
        self.assertEqual(profile['saving'], '7547360/10000000000')

    def test_untrusted_inputs_rejected(self):
        for key, value in [('repo_url', 'file:///etc/passwd'),
                           ('repo_url', 'https://user:secret@github.com/a/b'),
                           ('repo_url', 'https://github.com/a/b?x=y'),
                           ('commit', 'main'), ('commit', '-oops'),
                           ('challenge_file', '../submission/Challenge.lean'),
                           ('challenge_file', 'Work/Fourier233/UniformFourierChallenge.lean'),
                           ('theorem_names', 'True'),
                           ('theorem_names', 'OAI.PowerSaving.transform_mainY\n#eval IO.println "x"'),
                           ('lean_toolchain', 'nightly')]:
            with self.subTest(key=key, value=value):
                req = self.request(); req[key] = value
                with self.assertRaises(ValueError): v.validate_request(req)

    def test_trusted_challenge_is_independent(self):
        s = (ROOT / self.request()['challenge_file']).read_text()
        self.assertIn('import Mathlib', s)
        self.assertNotIn('import Work.', s)
        self.assertIn('def DFTProgram', s)
        self.assertIn('7547360/(10^(10:ℕ))', s)


class ChainTests(unittest.TestCase):
    def stage(self, files):
        tmp = tempfile.TemporaryDirectory(); self.addCleanup(tmp.cleanup)
        root = Path(tmp.name)
        for name, text in files.items():
            p = root / (name.replace('.', '/') + '.lean'); p.parent.mkdir(parents=True, exist_ok=True)
            p.write_text(text)
        return root

    def test_branches_stay_separate(self):
        root = self.stage({'X.A': 'import Mathlib\n', 'X.B': 'import X.A\n',
                           'X.C': 'import X.A\n', 'X.D': 'import X.B X.C\n'})
        self.assertEqual(v.plan_sources(root, 'X.D'), [['X.A', 'X.B'], ['X.C', 'X.D']])

    def test_nested_comments(self):
        root = self.stage({'X.A': '/- import Fake /- nested -/ -/\nimport Mathlib -- comment\n',
                           'X.B': 'import X.A\ntheorem b : True := by trivial\n'})
        self.assertEqual(v.plan_sources(root, 'X.B'), [['X.A', 'X.B']])

    def test_cycle_and_reserved_import(self):
        for files, target in [({'A': 'import B\n', 'B': 'import A\n'}, 'A'),
                              ({'A': 'import VerifierChallenge\n'}, 'A')]:
            with self.assertRaises(ValueError): v.plan_sources(self.stage(files), target)


class ReceiptStatusTests(unittest.TestCase):
    """verifier#194 (darkhipo): the receipt's status is the verdict's own rule, with each check's outcome apart."""
    NAME = 'BigOSpeedrun.Catalan.bound'

    def receipt(self, status='not_verified', lean='passed', nanoda=None, axioms=('propext',), stage='final'):
        nanoda = nanoda or {'status': 'incomplete', 'reason': 'out_of_memory'}
        data = {'status': status, 'theorem_names': [self.NAME], 'verification_stage': stage,
                'kernels': {'lean': {'status': lean, 'reason': 'comparator_acceptance'}, 'nanoda': nanoda},
                'axiom_audit': {'status': 'passed', 'reported_axioms': {self.NAME: list(axioms)}}}
        data['theorems'] = {self.NAME: {'lean_kernel': lean, 'nanoda_kernel': nanoda['status'], 'reported_axioms': list(axioms)}}
        return data

    def test_nanoda_out_of_memory_matches_the_verdict(self):
        # Run 43148643813 (#187): Lean and the audit passed, nanoda was OOM-killed; the receipt said not_verified.
        data = self.receipt(); v.receipt_status(data)
        self.assertEqual((data['status'], data['status_reason']), ('passed', 'lean_and_axiom_passed_nanoda_incomplete'))
        self.assertEqual(data['check_summary'], {'lean': 'passed (comparator_acceptance)', 'axiom_audit': 'passed',
                                                 'nanoda': 'incomplete (out_of_memory)'})

    def test_lean_checkpoint_passes_with_nanoda_queued(self):
        data = self.receipt(nanoda={'status': 'pending', 'reason': 'advisory_queued'}, stage='lean'); v.receipt_status(data)
        self.assertEqual((data['status'], data['status_reason']), ('passed', 'lean_and_axiom_passed_nanoda_pending'))

    def test_blocked_is_not_not_verified(self):
        data = self.receipt(axioms=('sorryAx',)); v.receipt_status(data)
        self.assertEqual((data['status'], data['status_reason']), ('blocked', 'unpermitted_axiom'))
        data = self.receipt(nanoda={'status': 'rejected'}); v.receipt_status(data)
        self.assertEqual(data['status'], 'blocked')

    def test_failed_lean_check_stays_not_verified(self):
        data = self.receipt(status='passed', lean='rejected'); v.receipt_status(data)
        self.assertEqual((data['status'], data['status_reason']), ('not_verified', 'lean_not_passed'))

    def test_setup_failure_and_timeout_keep_their_status(self):
        data = self.receipt(status='setup_failed'); v.receipt_status(data)
        self.assertEqual(data['status'], 'setup_failed'); self.assertNotIn('status_reason', data)
        data = self.receipt(status='timeout', lean='incomplete'); v.receipt_status(data)
        self.assertEqual(data['status'], 'timeout'); self.assertNotIn('status_reason', data)
        # A total deadline that only stopped the advisory nanoda check is the verdict's pass.
        data = self.receipt(status='timeout', nanoda={'status': 'incomplete', 'reason': 'total_deadline'}); v.receipt_status(data)
        self.assertEqual(data['status'], 'passed')


class ResourceReportTests(unittest.TestCase):
    GIB = 1024**3

    def test_3sat_build_at_the_cap_warns_and_a_78_percent_segment_does_not(self):
        # Run 43624031679 (#195): the 2-worker build peaked at the cap and was killed; the 1-worker retry peaked there too;
        # the longest Lean segment peaked at 11.8 GB (78%).
        cap = 14 * self.GIB
        data = {'build': {'sampled_peak_cgroup_bytes': cap, 'wall_seconds': 11371.3, 'attempts': [
                    {'lake_jobs': 2, 'sampled_peak_cgroup_bytes': cap, 'memory_limit_bytes': cap, 'wall_seconds': 10549.8},
                    {'lake_jobs': 1, 'sampled_peak_cgroup_bytes': cap, 'memory_limit_bytes': cap, 'wall_seconds': 821.4}]},
                'chain_export': {'sampled_peak_cgroup_bytes': 9.93e9, 'memory_limit_bytes': cap, 'wall_seconds': 160},
                'kernels': {'lean': {'status': 'passed', 'segments_detail': [
                    {'leg': 'check3', 'sampled_peak_cgroup_bytes': 5948358656, 'wall_seconds': 294},
                    {'leg': 'check4', 'sampled_peak_cgroup_bytes': 11765760000, 'wall_seconds': 1074}]}}}
        report = v.resource_report(data)
        self.assertTrue(report['warning'])
        self.assertEqual(report['warnings'], ['build attempt 1 (2 Lake workers): memory peak with page cache at 100% of its cap',
                                              'build attempt 2 (1 Lake workers): memory peak with page cache at 100% of its cap'])
        rows = {row['unit']: row for row in report['units']}
        self.assertEqual(rows['build attempt 1 (2 Lake workers)']['memory_peak_ratio'], 1.0)
        self.assertEqual(rows['lean segment check4']['memory_peak_ratio'], 0.783)
        self.assertEqual(rows['lean segment check4']['warn'], [])
        self.assertEqual(rows['chain_export']['memory_peak_ratio'], 0.661)
        self.assertEqual(rows['build attempt 1 (2 Lake workers)']['wall_ratio'], 0.525)

    def test_the_warning_reads_memory_without_page_cache(self):
        # Task 393f7f42: the split build peaks at the cap in memory.peak (page cache) on every run. With the no-cache peak
        # in the receipt the warning is silent at 40% and the raw ratio stays in the row.
        cap = 14 * self.GIB
        data = {'build': {'sampled_peak_cgroup_bytes': cap, 'sampled_peak_nocache_bytes': 5.6 * self.GIB, 'memory_limit_bytes': cap,
                          'wall_seconds': 100, 'attempts': [
                              {'lake_jobs': 2, 'sampled_peak_cgroup_bytes': cap, 'sampled_peak_nocache_bytes': 5.6 * self.GIB,
                               'memory_limit_bytes': cap, 'wall_seconds': 100}]}}
        report = v.resource_report(data)
        self.assertFalse(report['warning']); self.assertEqual(report['warnings'], [])
        row = report['units'][0]
        self.assertEqual((row['memory_peak_ratio'], row['memory_nocache_ratio'], row['warn']), (1.0, 0.4, []))
        # Anonymous memory near the cap does warn, and the text says what it counts.
        data['build']['attempts'][0]['sampled_peak_nocache_bytes'] = 12 * self.GIB
        self.assertEqual(v.resource_report(data)['warnings'],
                         ['build attempt 1 (2 Lake workers): memory without page cache at 86% of its cap'])

    def test_an_out_of_memory_kill_always_warns(self):
        # The no-cache peak is a 1-second sample, so a kill can show a low ratio (#195 and #205 killed the 2-worker 3-SAT build).
        cap = 14 * self.GIB
        attempts = [{'lake_jobs': 2, 'systemd_result': 'oom-kill', 'sampled_peak_cgroup_bytes': cap,
                     'sampled_peak_nocache_bytes': 7 * self.GIB, 'memory_limit_bytes': cap, 'wall_seconds': 100},
                    {'lake_jobs': 1, 'systemd_result': 'success', 'sampled_peak_cgroup_bytes': cap,
                     'sampled_peak_nocache_bytes': 7 * self.GIB, 'memory_limit_bytes': cap, 'wall_seconds': 100}]
        report = v.resource_report({'build': {'attempts': attempts}})
        self.assertEqual(report['warnings'], ['build attempt 1 (2 Lake workers): out-of-memory kill'])
        self.assertEqual(report['units'][0]['memory_nocache_ratio'], 0.5)
        self.assertEqual(report['units'][0]['warn'], ['oom']); self.assertEqual(report['units'][1]['warn'], [])
        # A segment, and a unit with no numbers at all, warn too; a high ratio gives both lines.
        data = {'kernels': {'lean': {'segments_detail': [{'leg': 'check2', 'systemd_result': 'oom-kill'}]}},
                'chain_export': {'systemd_result': 'oom-kill', 'sampled_peak_nocache_bytes': 13 * self.GIB, 'memory_limit_bytes': cap}}
        self.assertEqual(v.resource_report(data)['warnings'],
                         ['chain_export: memory without page cache at 93% of its cap', 'chain_export: out-of-memory kill',
                          'lean segment check2: out-of-memory kill'])
        self.assertEqual(v.resource_report({'build': {'attempts': [{'lake_jobs': 1, 'systemd_result': ['oom-kill']}]}})['warnings'], [])

    def test_nocache_bytes_sums_what_the_kernel_cannot_drop(self):
        text = '\n'.join(['anon 1000', 'file 99999', 'kernel 5000', 'kernel_stack 10', 'pagetables 20', 'sec_pagetables 0',
                          'percpu 30', 'sock 40', 'vmalloc 50', 'shmem 60', 'file_mapped 777', 'slab_reclaimable 888',
                          'slab_unreclaimable 70', 'slab 958', ''])
        self.assertEqual(v.nocache_bytes(text), 1000 + 10 + 20 + 0 + 30 + 40 + 50 + 60 + 70)
        self.assertEqual(v.nocache_bytes('anon 7\nfile 9\n'), 7)
        for bad in ['', 'file 9\n', 'anon x\n', 'anon \n']:
            self.assertIsNone(v.nocache_bytes(bad), bad)

    def test_sssp_peak_and_wall_and_swap_warn(self):
        # SSSP (#127): the Lean kernel peaked at 14.2 GB, 94% of the cap. Swap at its limit and a wall near the deadline too.
        data = {'kernels': {'lean': {'sampled_peak_cgroup_bytes': 14.2e9, 'wall_seconds': 335 * 60 * 0.9,
                                     'sampled_peak_swap_bytes': 16 * self.GIB, 'swap_limit_bytes': 16 * self.GIB}}}
        report = v.resource_report(data)
        self.assertEqual(report['warnings'], ['lean: memory peak with page cache at 94% of its cap', 'lean: swap at 100% of its cap',
                                              'lean: wall at 90% of the job deadline'])

    def test_a_receipt_without_numbers_or_with_bad_ones_has_no_warning(self):
        for data in [{}, {'build': None, 'kernels': {'lean': None, 'nanoda': {'status': 'incomplete'}}},
                     {'kernels': {'lean': {'sampled_peak_cgroup_bytes': 'x', 'wall_seconds': -1, 'segments_detail': [None, 3]}}}]:
            report = v.resource_report(data)
            self.assertFalse(report['warning']); self.assertEqual(report['warnings'], [])

    def test_values_that_are_not_finite_numbers_are_skipped(self):
        # json.loads reads Infinity, NaN and an integer of any size; a bool is not a number here.
        for bad in [float('inf'), float('nan'), 10**400, True, -1, 2**64, 'x', None]:
            data = {'build': {'sampled_peak_cgroup_bytes': bad, 'memory_limit_bytes': bad, 'wall_seconds': bad,
                              'sampled_peak_swap_bytes': bad, 'swap_limit_bytes': bad, 'attempts': [
                                  {'lake_jobs': bad, 'sampled_peak_cgroup_bytes': bad, 'wall_seconds': bad}]},
                    'kernels': {'lean': {'segments_detail': [{'leg': bad, 'sampled_peak_cgroup_bytes': bad, 'wall_seconds': bad}]}}}
            report = v.resource_report(data)
            self.assertFalse(report['warning'], bad); self.assertEqual(report['warnings'], [])
        # A bad limit falls back to the cap; a bad peak skips the ratio.
        report = v.resource_report({'build': {'sampled_peak_cgroup_bytes': 14 * self.GIB, 'memory_limit_bytes': float('inf')}})
        self.assertEqual(report['warnings'], ['build: memory peak with page cache at 100% of its cap'])

    def test_unit_names_from_receipt_values_are_plain(self):
        data = {'build': {'attempts': [{'lake_jobs': '[x](http://e)', 'sampled_peak_cgroup_bytes': 14 * self.GIB}]},
                'kernels': {'a b\n#': {'segments_detail': [{'leg': '<img src=x>', 'sampled_peak_cgroup_bytes': 14 * self.GIB}]}}}
        self.assertEqual(v.resource_report(data)['warnings'], ['build attempt 1 (? Lake workers): memory peak with page cache at 100% of its cap',
                                                               '? segment ?: memory peak with page cache at 100% of its cap'])

    def test_finalize_survives_a_report_that_fails(self):
        import os
        from unittest import mock
        old = (v.ART, os.environ.get('GITHUB_STEP_SUMMARY'))
        with tempfile.TemporaryDirectory() as folder, mock.patch.object(v, 'resource_report', side_effect=OverflowError('x')):
            try:
                v.ART = Path(folder)
                os.environ.pop('GITHUB_STEP_SUMMARY', None)
                v.save({'schema_version': 1, 'status': 'setup_failed', 'steps': [], 'kernels': {}})
                v.finalize()
                data = v.receipt()
            finally:
                v.ART = old[0]
                if old[1] is not None: os.environ['GITHUB_STEP_SUMMARY'] = old[1]
        self.assertEqual(data['status'], 'setup_failed'); self.assertIn('artifact_sha256', data)
        self.assertEqual(data['resource_report']['error'], 'resource_report_failed')

    def test_the_finalized_receipt_carries_the_report(self):
        import os
        old = (v.ART, os.environ.get('GITHUB_STEP_SUMMARY'))
        with tempfile.TemporaryDirectory() as folder:
            try:
                v.ART = Path(folder)
                os.environ.pop('GITHUB_STEP_SUMMARY', None)
                v.save({'schema_version': 1, 'status': 'setup_failed', 'steps': [], 'kernels': {},
                        'build': {'sampled_peak_cgroup_bytes': 14 * self.GIB, 'wall_seconds': 60}})
                v.finalize()
                data = v.receipt()
            finally:
                v.ART = old[0]
                if old[1] is not None: os.environ['GITHUB_STEP_SUMMARY'] = old[1]
        self.assertTrue(data['resource_report']['warning'])
        self.assertEqual(data['resource_report']['warnings'], ['build: memory peak with page cache at 100% of its cap'])


if __name__ == '__main__': unittest.main()
