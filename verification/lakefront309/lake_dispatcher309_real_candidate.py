"""Unexecuted source-only real-heavy dispatcher candidate for parent review.

This program never fabricates compiler artifacts, Lake traces or Built messages.
The exact manifest-bound heavy call uses the frozen cached driver file; every
other call runs the stock executable with the original argv. Execution requires
an explicit, frozen LAKEFRONT309_CONFIG created by the root launcher.
The running toy dispatcher is a separate immutable file. This candidate has not
been connected to a bridge, executed, or accepted as a proof certificate.
"""
from __future__ import annotations

import datetime as dt
import codecs
from collections import deque
import hashlib
import json
import os
from pathlib import Path
import re
import stat
import subprocess
import sys
import threading
import time
import uuid

HERE = Path(__file__).resolve().parent
LOWINFO = HERE.parent / 'lowinfo309'
DRIVER_ROOTS = (LOWINFO, HERE.parent / 'lowinfo309_cached', HERE / 'driver_variants')
MODULE = 'RiemannZeta.GuthMaynard.HughesYoungActiveComplementSourceLine'
PACKAGE = 'GafniTaoFrozen'
LIBRARY = 'RiemannZeta'
MODE = 'frozen_gafnitao_riemann_heavy'
MODULE_PATH = Path(*MODULE.split('.'))
SOURCE_SHA256 = 'a39dd8053b3c5ecfe24d673fddb4965e8d355d2d584dc1ef0a3407e3a14f6a9b'
SOURCE_BYTES = 415362
DRIVER_SHA256 = '26f73083d233b617829bbf790dcfb8cda4a1a821f9b5e12776ef2cda38d35b16'
STOCK_SHA256 = '8132256d484b8ecc4561bec70abd1271f4c0d03badbc3bc272f6c4053af9fdbc'
BASELINE_REPORT_SHA256 = '15facfcaa360ae685ad43e9d25076e8e0cb57abc95377709d77b6b53ec6d6fd7'
BASELINE_REQUEST_SHA256 = 'e3d5ce1ea103d235e6d5fcfd81a98dc7b5545b707b28d6034b55f5c0dd660df1'
WEAK_PREFIX = ['-DElab.async=false', '-j1']
STD3 = frozenset(('propext', 'Classical.choice', 'Quot.sound'))
EXPECTED_SETUP_OPTIONS = {'pp.unicode.fun': True, 'autoImplicit': False}
REQUEST_FIELDS = frozenset(('source', 'setup', 'sysroot', 'olean', 'ilean', 'cFile',
    'report', 'cmdlineOptions', 'cliPlugins', 'infoEnabled', 'failOnWarnings',
    'expectedNames', 'postExportCachedAxioms', 'provisionalOlean',
    'expectedHeavySource', 'prewarmSymbolFrequency', 'metadataMaxHeartbeats'))
REPORT_FIELDS = frozenset(('status', 'module', 'source_bytes', 'eof_byte', 'counts',
    'trust_level', 'skip_kernel_tc', 'check_kernel', 'info_enabled_per_command',
    'info_dependent_linters_have_inputs', 'kernel_declarations', 'module_system',
    'ilean_semantic_equivalence_to_stock'))
CACHED_REPORT_FIELDS = frozenset(('post_export_cached_axioms',
    'symbol_frequency_metadata_warmed', 'metadata_max_heartbeats',
    'metadata_export_heartbeat_baseline_reset'))
SCHEMA = 'lakefront309.real-heavy.dispatch.v1'
IDENTITY_ENV_KEYS = ('LAKEFRONT309_CONFIG', 'LAKEFRONT309_BRIDGE_POLICY',
                     'LEAN', 'LEAN_SYSROOT', 'LEAN_GITHASH',
                     'LEAN_PATH', 'LEAN_SRC_PATH', 'LEAN_NUM_THREADS',
                     'LAKE_OVERRIDE_LEAN', 'LAKE_ARTIFACT_CACHE')
RAW_PANIC_SUFFIX = re.compile(r'\bPANIC$', re.IGNORECASE)
RAW_INVALID_PREFIX = re.compile(r'\binvalid$', re.IGNORECASE)
RAW_DETERMINISTIC_SUFFIX = re.compile(r'\(deterministic\)$', re.IGNORECASE)
RAW_TIMEOUT_CHARACTERS = tuple(re.compile(re.escape(c), re.IGNORECASE) for c in 'timeout')
RAW_MESSAGE_CHARACTERS = tuple(re.compile(re.escape(c), re.IGNORECASE) for c in 'MessageData')
RAW_FATAL_CONTRACT = r'\bPANIC\b|\(deterministic\)\s+timeout\b|\binvalid\s+MessageData\b'


def utc():
    return dt.datetime.now(dt.timezone.utc).isoformat()


def canonical(path):
    return Path(path).resolve()


def digest(path):
    result = hashlib.sha256()
    with Path(path).open('rb') as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b''):
            result.update(chunk)
    return result.hexdigest()


def valid_sha(value):
    return isinstance(value, str) and len(value) == 64 and all(c in '0123456789abcdef' for c in value)


def configured_driver(value):
    """Bind an absolute regular Lean source within the three literal owned roots.

    Resolve the selected file, not the whitelist roots: a root/child symlink
    escaping the literal verification directories must not expand authorization.
    The canonical path is used for every snapshot and the real --run argument.
    """
    if not isinstance(value, str) or not value or not Path(value).is_absolute():
        raise ValueError('driver_path must be an absolute Lean source path')
    path = Path(value).resolve(strict=True)
    if not any(path.is_relative_to(root) for root in DRIVER_ROOTS):
        raise ValueError('Configured driver is outside the three authorized verification directories')
    if path.suffix.lower() != '.lean' or not stat.S_ISREG(path.stat().st_mode):
        raise ValueError('Configured driver must be an existing regular .lean source file')
    return path


def frontend_command(stock, selected_driver, request_path):
    """The selected, frozen source is the executable Lean --run input."""
    return [str(stock), '-t0', '-j1', '-DElab.async=false', '--run',
            str(selected_driver), str(request_path)]


def absolute_path(value, *, regular=False, directory=False):
    if not isinstance(value, str) or not value or not Path(value).is_absolute():
        raise ValueError('Configured paths must be explicit absolute strings')
    path = Path(value).resolve(strict=regular or directory)
    if regular and not stat.S_ISREG(path.stat().st_mode):
        raise ValueError('Expected an existing regular file: ' + value)
    if directory and not stat.S_ISDIR(path.stat().st_mode):
        raise ValueError('Expected an existing directory: ' + value)
    return path


def evidence_path(value):
    path = absolute_path(value, regular=True)
    if not path.is_relative_to(HERE.parent) or path.suffix.lower() != '.json':
        raise ValueError('Baseline evidence must be an existing JSON file in owned verification')
    return path


def owned(path):
    result = canonical(path)
    if not result.is_relative_to(HERE):
        raise ValueError('Dispatcher sidecar path is outside lakefront309: ' + str(path))
    return result


def save_json(path, value):
    path = owned(path)
    temporary = owned(path.with_name(path.name + '.' + uuid.uuid4().hex + '.tmp'))
    data = (json.dumps(value, ensure_ascii=False, indent=2) + '\n').encode('utf-8')
    with temporary.open('xb') as stream:
        stream.write(data)
        stream.flush()
        os.fsync(stream.fileno())
    for attempt in range(7):
        try:
            os.replace(temporary, path)
            return
        except PermissionError:
            if attempt == 6:
                raise
            time.sleep(0.05 * (2 ** attempt))


def snapshot(path):
    path = canonical(path)
    try:
        return {'path': str(path), 'exists': True, 'bytes': path.stat().st_size, 'sha256': digest(path)}
    except FileNotFoundError:
        return {'path': str(path), 'exists': False}


def safe_stderr(message):
    try:
        if sys.stderr is not None:
            sys.stderr.write(message + '\n')
            sys.stderr.flush()
    except Exception:
        pass


def dispatch_code(child_code, rejected=False, fallback=64):
    """A logger/validation error must never replace an observed child failure."""
    if child_code is not None and child_code != 0:
        return child_code
    return fallback if rejected or child_code is None else 0


def scan_raw_stream(stream, chunk_size=65536):
    """Exact text contract, Unicode word/space rules, CSI normalization, raw SHA.

    The deterministic whitespace run has a finite-state counter, not a bounded
    regex tail: arbitrary whitespace/chunk boundaries cannot truncate a match.
    Strict UTF-8 decoding rejects undecodable output; raw bytes/SHA stay intact.
    """
    if type(chunk_size) is not int or chunk_size <= 0:
        raise ValueError('Raw scanner chunk_size must be a positive integer')
    total = 0
    checksum = hashlib.sha256()
    first = {}
    history = deque(maxlen=64)
    pending = {}
    active = {}
    decoder = codecs.getincrementaldecoder('utf-8')(errors='strict')
    decoded_offset = 0
    ansi_state = 'normal'
    ansi_offset = None

    def remember(kind, offset, text, **details):
        if kind not in first or offset < first[kind]['byte_offset']:
            first[kind] = {'kind': kind, 'byte_offset': offset, 'matched_text': text,
                           'normalized_excerpt': ''.join(c for c, _ in history), **details}

    def text_character(character, offset):
        for kind, candidate in list(pending.items()):
            if not (character.isalnum() or character == '_'):
                remember(kind, candidate['offset'], candidate['text'], **candidate['details'])
            del pending[kind]
        for kind, sequence in list(active.items()):
            if sequence['position'] is None:
                if character.isspace():
                    sequence['spaces'] += 1
                elif sequence['spaces'] and sequence['characters'][0].fullmatch(character):
                    sequence['position'] = 1
                else:
                    del active[kind]
            else:
                position = sequence['position']
                if sequence['characters'][position].fullmatch(character):
                    sequence['position'] += 1
                    if sequence['position'] == len(sequence['characters']):
                        pending[kind] = {'offset': sequence['offset'], 'text': sequence['text'],
                                         'details': {'whitespace_characters': sequence['spaces']}}
                        del active[kind]
                else:
                    del active[kind]
        history.append((character, offset))
        # Only these suffix characters can complete a bounded literal prefix.
        if character in 'cCdD)':
            text = ''.join(c for c, _ in history)
            positions = [p for _, p in history]
            if character in 'cC':
                match = RAW_PANIC_SUFFIX.search(text)
                if match is not None:
                    pending['panic'] = {'offset': positions[match.start()], 'text': match.group(), 'details': {}}
            if character in 'dD':
                match = RAW_INVALID_PREFIX.search(text)
                if match is not None:
                    active['invalid_message_data'] = {
                        'offset': positions[match.start()], 'spaces': 0, 'position': None,
                        'characters': RAW_MESSAGE_CHARACTERS, 'text': 'invalid <whitespace> MessageData'}
            if character == ')':
                match = RAW_DETERMINISTIC_SUFFIX.search(text)
                if match is not None:
                    active['deterministic_timeout'] = {
                        'offset': positions[match.start()], 'spaces': 0, 'position': None,
                        'characters': RAW_TIMEOUT_CHARACTERS, 'text': '(deterministic) <whitespace> timeout'}

    def normalized_character(character, offset):
        nonlocal ansi_state, ansi_offset
        if ansi_state == 'normal':
            if character == '\x1b':
                ansi_state, ansi_offset = 'escape', offset
            else:
                text_character(character, offset)
        elif ansi_state == 'escape':
            if character == '[':
                ansi_state = 'csi_parameters'
            else:
                text_character('\x1b', ansi_offset)
                ansi_state = 'normal'
                normalized_character(character, offset)
        elif ('@' <= character <= '~'):
            ansi_state = 'normal'  # A complete standard ANSI CSI sequence.
        elif ansi_state == 'csi_parameters' and ('0' <= character <= '?'):
            pass
        elif ' ' <= character <= '/':
            ansi_state = 'csi_intermediates'
        else:
            # Invalid CSI text cannot hide a diagnostic or join separate words.
            # Parameter/intermediate bytes contain no diagnostic letters; retain
            # the prefix delimiter with bounded memory instead of a huge buffer.
            text_character('\x1b', ansi_offset)
            text_character('[', ansi_offset + 1)
            ansi_state = 'normal'
            normalized_character(character, offset)

    def decoded_text(text):
        nonlocal decoded_offset
        for character in text:
            offset = decoded_offset
            decoded_offset += len(character.encode('utf-8'))
            normalized_character(character, offset)

    while True:
        block = stream.read(chunk_size)
        if not block:
            break
        checksum.update(block)
        total += len(block)
        decoded_text(decoder.decode(block))
    decoded_text(decoder.decode(b'', final=True))
    if ansi_state != 'normal':
        text_character('\x1b', ansi_offset)
        if ansi_state != 'escape':
            text_character('[', ansi_offset + 1)
    for kind, candidate in pending.items():
        remember(kind, candidate['offset'], candidate['text'], **candidate['details'])
    if decoded_offset != total:
        raise ValueError('Raw scanner UTF-8 byte-offset accounting mismatch')
    return {'bytes_scanned': total, 'sha256': checksum.hexdigest(), 'reached_eof': True,
            'fatal_matches': sorted(first.values(), key=lambda hit: (hit['byte_offset'], hit['kind']))}


def scan_raw_logs(logs):
    scans = []
    hits = []
    errors = []
    for channel in ('stdout', 'stderr', 'merged'):
        row = {'stream': channel, 'reached_eof': False}
        try:
            recorded = logs[channel]
            path = owned(recorded['path'])
            row['path'] = str(path)
            with path.open('rb') as stream:
                scanned = scan_raw_stream(stream)
            row.update(scanned)
            hits.extend({'stream': channel, 'path': str(path), **hit} for hit in scanned['fatal_matches'])
            if scanned['sha256'] != recorded.get('sha256') or scanned['bytes_scanned'] != recorded.get('bytes'):
                raise ValueError('Captured raw log bytes changed before full fatal scan: ' + channel)
        except Exception as error:
            row['scan_error'] = repr(error)
            errors.append('Raw log full scan failed for ' + channel + ': ' + repr(error))
        scans.append(row)
    return {'schema': 'lakefront309.fatal_raw_gate.v2',
            'policy': RAW_FATAL_CONTRACT, 'case_insensitive': True,
            'ansi_normalization': 'Standard CSI sequences removed across chunks; other escapes preserved',
            'entire_raw_files_scanned': all(row['reached_eof'] for row in scans),
            'passed': not hits and not errors, 'scans': scans, 'fatal_matches': hits, 'scan_errors': errors}


def declaration_map(audit, *, cached=False):
    fields = {'count', 'entries'}
    if cached:
        fields |= {'audit_method', 'inventory_signature_equivalent',
                   'proof_body_equality_checked', 'module_index'}
    if not isinstance(audit, dict) or set(audit) != fields:
        raise ValueError('Unexpected complete declaration audit schema')
    if type(audit['count']) is not int or audit['count'] != 225:
        raise ValueError('Expected exactly 225 original kernel declarations')
    if not isinstance(audit['entries'], list) or len(audit['entries']) != 225:
        raise ValueError('Expected exactly 225 complete declaration rows')
    result = {}
    for row in audit['entries']:
        if not isinstance(row, dict) or set(row) != {'name', 'axioms'}:
            raise ValueError('Unexpected declaration row schema')
        name, axes = row['name'], row['axioms']
        if not isinstance(name, str) or not name or name in result:
            raise ValueError('Missing or duplicate kernel declaration name')
        if not isinstance(axes, list) or not all(isinstance(ax, str) for ax in axes):
            raise ValueError('Declaration axioms must be an explicit string array')
        if len(axes) != len(set(axes)) or not set(axes).issubset(STD3):
            raise ValueError('Duplicate or unsupported declaration axiom dependency')
        result[name] = frozenset(axes)
    if cached:
        if audit['audit_method'] != 'stock_exported_axioms_reimport_all_original_constants':
            raise ValueError('Unexpected cached audit method')
        if audit['inventory_signature_equivalent'] is not True or audit['proof_body_equality_checked'] is not False:
            raise ValueError('Cached signature/proof-body evidence boundary mismatch')
        if type(audit['module_index']) is not int or audit['module_index'] < 0:
            raise ValueError('Cached module index must be a nonnegative integer')
    return result


def validate_report_payload(report, *, cached=False, reference=None):
    required = REPORT_FIELDS | CACHED_REPORT_FIELDS if cached else REPORT_FIELDS
    if not isinstance(report, dict) or set(report) != required:
        raise ValueError('Unexpected complete driver report schema')
    if report['status'] != 'prototype_completed_not_acceptance' or report['module'] != MODULE:
        raise ValueError('Driver report status/module mismatch')
    for key in ('source_bytes', 'eof_byte'):
        if type(report[key]) is not int or report[key] != SOURCE_BYTES:
            raise ValueError('Driver report must bind complete original source bytes: ' + key)
    if type(report['trust_level']) is not int or report['trust_level'] != 0:
        raise ValueError('Driver report kernel trust level mismatch')
    for key, expected in (('skip_kernel_tc', False), ('check_kernel', True),
                          ('info_enabled_per_command', True), ('info_dependent_linters_have_inputs', True),
                          ('module_system', False)):
        if report[key] is not expected:
            raise ValueError('Driver report boundary mismatch: ' + key)
    if report['ilean_semantic_equivalence_to_stock'] != 'not_yet_verified':
        raise ValueError('Unexpected ilean evidence claim')
    counts = report['counts']
    expected_counts = {'commands': 211, 'errors': 0, 'warnings': 0}
    if not isinstance(counts, dict) or set(counts) != set(expected_counts):
        raise ValueError('Driver report count schema mismatch')
    for key, expected in expected_counts.items():
        if type(counts[key]) is not int or counts[key] != expected:
            raise ValueError('Driver report original command/error/warning count mismatch: ' + key)
    declarations = declaration_map(report['kernel_declarations'], cached=cached)
    if reference is not None and declarations != reference:
        raise ValueError('All 225 declaration names/individual axiom closures differ from frozen original report')
    if cached:
        for key in ('post_export_cached_axioms', 'symbol_frequency_metadata_warmed',
                    'metadata_export_heartbeat_baseline_reset'):
            if report[key] is not True:
                raise ValueError('Missing genuine cached-export boundary flag: ' + key)
        if type(report['metadata_max_heartbeats']) is not int or report['metadata_max_heartbeats'] != 20000000:
            raise ValueError('Metadata heartbeat budget is not the explicit finite 20000000')
    return declarations


def baseline_payloads(report_raw, request_raw):
    report = json.loads(report_raw.decode('utf-8'))
    declaration_axes = validate_report_payload(report)
    request = json.loads(request_raw.decode('utf-8'))
    if not isinstance(request, dict) or set(request) != REQUEST_FIELDS - {
            'postExportCachedAxioms', 'provisionalOlean', 'expectedHeavySource',
            'prewarmSymbolFrequency', 'metadataMaxHeartbeats'}:
        raise ValueError('Unexpected frozen original request schema')
    names = request['expectedNames']
    if (not isinstance(names, list) or len(names) != 194
            or not all(isinstance(name, str) and name for name in names)
            or len(set(names)) != 194 or not set(names).issubset(declaration_axes)):
        raise ValueError('Frozen original request must name 194 unique original kernel declarations')
    if (request['cmdlineOptions'] != {'Elab.async': False}
            or request['cmdlineOptions'].get('Elab.async') is not False
            or request['cliPlugins'] != [] or request['infoEnabled'] is not True
            or request['failOnWarnings'] is not True):
        raise ValueError('Frozen original request policy mismatch')
    return names, declaration_axes


def validate_template(request, target, paths, expected_names):
    if not isinstance(request, dict) or set(request) != REQUEST_FIELDS:
        raise ValueError('Cached Request must explicitly supply all 17 fields and no unknown fields')
    path_fields = {'source': paths['source'], 'setup': paths['setup'], 'sysroot': paths['sysroot'],
                   'olean': paths['artifacts']['olean'], 'ilean': paths['artifacts']['ilean'],
                   'cFile': paths['artifacts']['c'], 'expectedHeavySource': paths['source']}
    for key, expected in path_fields.items():
        if absolute_path(request[key]) != expected:
            raise ValueError('Request path does not match the frozen configured target: ' + key)
    if request['report'] != '@CALL/frontend.report.json' or request['provisionalOlean'] != '@CALL/heavy.provisional.olean':
        raise ValueError('Report/provisional paths must use the exact unique-owned-call placeholders')
    if (not isinstance(request['cmdlineOptions'], dict) or set(request['cmdlineOptions']) != {'Elab.async'}
            or request['cmdlineOptions']['Elab.async'] is not False):
        raise ValueError('Cached request must explicitly preserve Elab.async=false')
    if request['cliPlugins'] != []:
        raise ValueError('Unknown command-line plugins are not authorized')
    for key in ('infoEnabled', 'failOnWarnings', 'postExportCachedAxioms', 'prewarmSymbolFrequency'):
        if request[key] is not True:
            raise ValueError('Cached request requires strict true policy: ' + key)
    if type(request['metadataMaxHeartbeats']) is not int or request['metadataMaxHeartbeats'] != 20000000:
        raise ValueError('Cached request metadata budget must be the integer 20000000')
    if request['expectedNames'] != expected_names:
        raise ValueError('Cached request must retain the exact frozen original ordered 194 names')
    return path_fields


def load_config():
    configured = os.environ.get('LAKEFRONT309_CONFIG')
    if not configured:
        raise ValueError('LAKEFRONT309_CONFIG must identify a root-frozen real-heavy configuration')
    config_path = owned(configured)
    raw = config_path.read_bytes()
    config = json.loads(raw.decode('utf-8'))
    fields = {'schema', 'mode', 'sysroot', 'stock_lean', 'stock_lean_sha256',
              'driver_path', 'driver_sha256', 'evidence', 'target', 'request_template'}
    if not isinstance(config, dict) or set(config) != fields or config['schema'] != SCHEMA or config['mode'] != MODE:
        raise ValueError('Unexpected real-heavy configuration fields/schema/mode')
    if config['stock_lean_sha256'] != STOCK_SHA256 or config['driver_sha256'] != DRIVER_SHA256:
        raise ValueError('This candidate accepts only the exact official Lean executable and frozen cached driver SHAs')
    sysroot = absolute_path(config['sysroot'], directory=True)
    stock = absolute_path(config['stock_lean'], regular=True)
    if stock != sysroot / 'bin' / 'lean.exe':
        raise ValueError('Configured stock Lean must be the canonical sysroot/bin/lean.exe; PATH is never searched')
    driver = configured_driver(config['driver_path'])
    if digest(stock) != STOCK_SHA256 or digest(driver) != DRIVER_SHA256:
        raise ValueError('Actual stock Lean/cached driver bytes differ from the exact frozen SHAs')
    evidence = config['evidence']
    if not isinstance(evidence, dict) or set(evidence) != {'report', 'report_sha256', 'request', 'request_sha256'}:
        raise ValueError('Unexpected frozen baseline evidence fields')
    if evidence['report_sha256'] != BASELINE_REPORT_SHA256 or evidence['request_sha256'] != BASELINE_REQUEST_SHA256:
        raise ValueError('Baseline evidence must bind the exact original report/request SHAs')
    baseline_report = evidence_path(evidence['report'])
    baseline_request = evidence_path(evidence['request'])
    report_raw, request_raw = baseline_report.read_bytes(), baseline_request.read_bytes()
    if hashlib.sha256(report_raw).hexdigest() != BASELINE_REPORT_SHA256 or hashlib.sha256(request_raw).hexdigest() != BASELINE_REQUEST_SHA256:
        raise ValueError('Actual original report/request bytes differ from frozen evidence')
    expected_names, declaration_axes = baseline_payloads(report_raw, request_raw)
    target = config['target']
    target_fields = {'package', 'library', 'module', 'cwd', 'source', 'source_sha256', 'source_bytes',
                     'setup', 'setup_sha256', 'setup_options', 'build_root', 'artifacts', 'prefix_args'}
    if not isinstance(target, dict) or set(target) != target_fields:
        raise ValueError('Unexpected real-heavy target fields')
    if (target['package'] != PACKAGE or target['library'] != LIBRARY or target['module'] != MODULE
            or target['source_sha256'] != SOURCE_SHA256 or type(target['source_bytes']) is not int
            or target['source_bytes'] != SOURCE_BYTES or not valid_sha(target['setup_sha256'])
            or target['prefix_args'] != WEAK_PREFIX):
        raise ValueError('Target package/library/module/source/prefix differs from the fixed authorized heavy mode')
    cwd = absolute_path(target['cwd'], directory=True)
    source = absolute_path(target['source'], regular=True)
    build_root = absolute_path(target['build_root'], directory=True)
    setup = absolute_path(target['setup'], regular=True)
    source_relative = Path('FrozenFoundation') / MODULE_PATH.with_suffix('.lean')
    if Path(*source.parts[-len(source_relative.parts):]) != source_relative:
        raise ValueError('Heavy source does not retain the exact portable FrozenFoundation module path suffix')
    if setup != build_root / 'ir' / MODULE_PATH.with_suffix('.setup.json'):
        raise ValueError('Setup is not the exact official module artifact path')
    if source.stat().st_size != SOURCE_BYTES or digest(source) != SOURCE_SHA256 or digest(setup) != target['setup_sha256']:
        raise ValueError('Heavy source bytes/size or complete setup SHA mismatch')
    options = target['setup_options']
    if not isinstance(options, dict) or set(options) != set(EXPECTED_SETUP_OPTIONS):
        raise ValueError('Unexpected exact setup option inventory')
    if any(options[key] is not expected for key, expected in EXPECTED_SETUP_OPTIONS.items()):
        raise ValueError('Exact setup option values must retain the original stock package policy')
    artifacts = {'olean': build_root / 'lib' / 'lean' / MODULE_PATH.with_suffix('.olean'),
                 'ilean': build_root / 'lib' / 'lean' / MODULE_PATH.with_suffix('.ilean'),
                 'c': build_root / 'ir' / MODULE_PATH.with_suffix('.c')}
    if not isinstance(target['artifacts'], dict) or set(target['artifacts']) != set(artifacts):
        raise ValueError('Expected exactly the three official olean/ilean/C output paths')
    for key, expected in artifacts.items():
        if absolute_path(target['artifacts'][key]) != expected:
            raise ValueError('Artifact path differs from official stock module facet: ' + key)
    paths = {'source': source, 'setup': setup, 'sysroot': sysroot, 'stock': stock, 'driver': driver,
             'cwd': cwd, 'build_root': build_root, 'artifacts': artifacts,
             'baseline_report': baseline_report, 'baseline_request': baseline_request,
             'expected_names': expected_names, 'declaration_axes': declaration_axes}
    validate_template(config['request_template'], target, paths, expected_names)
    return config_path, raw, config, paths


def observes_heavy(argv, target):
    return any(value.lower().endswith('.lean') and canonical(value) == canonical(target['source']) for value in argv)


def parse_heavy_tokens(argv, target):
    if len(argv) != 12 or argv[:2] != WEAK_PREFIX or canonical(argv[2]) != canonical(target['source']):
        raise ValueError('Heavy argv must retain the exact two weak args and complete twelve-token stock call')
    if argv[3] != '-o' or argv[5] != '-i' or argv[7] != '-c' or argv[9] != '--setup' or argv[11] != '--json':
        raise ValueError('Heavy artifact/setup/json flags or their official order differ from the authorized call')
    for key, index in (('olean', 4), ('ilean', 6), ('c', 8)):
        if canonical(argv[index]) != canonical(target['artifacts'][key]):
            raise ValueError('Heavy requested an unexpected official artifact: ' + key)
    if canonical(argv[10]) != canonical(target['setup']):
        raise ValueError('Heavy requested an unexpected setup path')
    return {'source': str(canonical(argv[2])), 'setup': str(canonical(argv[10])),
            'artifacts': {key: str(canonical(argv[index])) for key, index in (('olean', 4), ('ilean', 6), ('c', 8))}}


def parse_heavy(argv, target, paths):
    parse_heavy_tokens(argv, target)
    source = snapshot(paths['source'])
    if source.get('sha256') != SOURCE_SHA256 or source.get('bytes') != SOURCE_BYTES:
        raise ValueError('Heavy original source bytes differ from the exact frozen size/SHA')
    setup_raw = paths['setup'].read_bytes()
    if hashlib.sha256(setup_raw).hexdigest() != target['setup_sha256']:
        raise ValueError('Complete actual setup SHA differs from the frozen configuration')
    setup = json.loads(setup_raw.decode('utf-8'))
    if (not isinstance(setup, dict) or set(setup) != {'plugins', 'package', 'options', 'name', 'isModule', 'importArts', 'dynlibs'}
            or setup['name'] != MODULE or setup['package'] != PACKAGE or setup['isModule'] is not False
            or setup['plugins'] != [] or setup['dynlibs'] != [] or not isinstance(setup['importArts'], dict)):
        raise ValueError('Complete setup schema/module/package/nonmodule/plugin policy differs from the actual stock facet')
    options = setup['options']
    if not isinstance(options, dict) or set(options) != set(EXPECTED_SETUP_OPTIONS):
        raise ValueError('Actual setup options must retain the exact original two stock options')
    if any(options[key] is not expected for key, expected in EXPECTED_SETUP_OPTIONS.items()):
        raise ValueError('Actual setup option values differ from the frozen original package policy')
    for output in paths['artifacts'].values():
        if output.exists() or output.with_name(output.name + '.publish-pending').exists():
            raise ValueError('Lake must supply fresh final outputs before this compile call: ' + str(output))
    return {'source': source, 'setup': {'path': str(paths['setup']), 'exists': True,
                                      'bytes': len(setup_raw), 'sha256': hashlib.sha256(setup_raw).hexdigest()},
            'module': MODULE, 'package': PACKAGE, 'library': LIBRARY, 'setup_options': options,
            'original_weak_prefix_args': list(WEAK_PREFIX),
            'artifacts': {key: str(path) for key, path in paths['artifacts'].items()}}


def materialize_request(template, paths, call_dir):
    call_dir = owned(call_dir)
    report = owned(call_dir / 'frontend.report.json')
    provisional = owned(call_dir / 'heavy.provisional.olean')
    for output in (report, provisional, provisional.with_name(provisional.name + '.c'),
                   provisional.with_name(provisional.name + '.ilean'), provisional.with_name(provisional.name + '.ir')):
        if output.exists():
            raise ValueError('Fresh call report/provisional output already exists: ' + str(output))
    request = dict(template)
    for key, path in (('source', paths['source']), ('setup', paths['setup']), ('sysroot', paths['sysroot']),
                      ('olean', paths['artifacts']['olean']), ('ilean', paths['artifacts']['ilean']),
                      ('cFile', paths['artifacts']['c']), ('expectedHeavySource', paths['source'])):
        request[key] = str(path)
    request['report'], request['provisionalOlean'] = str(report), str(provisional)
    return request, report, provisional


def observe_stock_paths(argv):
    paths = {}
    consumed = set()
    for index, value in enumerate(argv[:-1]):
        if value in ('--setup', '-o', '-i', '-c', '-b'):
            paths[value + ':' + str(index)] = canonical(argv[index + 1])
            consumed.add(index + 1)
    for index, value in enumerate(argv):
        if index not in consumed and value.lower().endswith('.lean') and not value.startswith('-'):
            paths['source:' + str(index)] = canonical(value)
    return paths


def tee_child(command, call_dir, record, record_path):
    stdout_path = call_dir / 'stdout.raw.log'
    stderr_path = call_dir / 'stderr.raw.log'
    merged_path = call_dir / 'child.raw.log'
    index_path = call_dir / 'raw_segments.jsonl'
    errors = []
    lock = threading.Lock()
    ready = threading.Event()
    child = None
    with stdout_path.open('xb') as outlog, stderr_path.open('xb') as errlog, \
            merged_path.open('xb') as merged, index_path.open('x', encoding='utf-8', newline='\n') as segments:
        # Resolve forward streams and start both waiting drain threads before
        # Popen. If a stream or thread cannot be initialized there is no child.
        parents = (sys.stdout.buffer, sys.stderr.buffer)

        def pump(rawlog, parent, channel):
            ready.wait()
            if child is None:
                return
            pipe = child.stdout if channel == 'stdout' else child.stderr
            log_ok = parent_ok = True
            offset = 0
            try:
                while True:
                    block = pipe.read1(65536)
                    if not block:
                        break
                    with lock:
                        if log_ok:
                            try:
                                merged_offset = merged.tell()
                                rawlog.write(block)
                                rawlog.flush()
                                os.fsync(rawlog.fileno())
                                merged.write(block)
                                merged.flush()
                                os.fsync(merged.fileno())
                                segments.write(json.dumps({'utc': utc(), 'stream': channel, 'stream_offset': offset,
                                                           'merged_offset': merged_offset, 'bytes': len(block)}, separators=(',', ':')) + '\n')
                                segments.flush()
                                os.fsync(segments.fileno())
                            except Exception as error:
                                errors.append(channel + '_log: ' + repr(error))
                                log_ok = False
                        if parent_ok:
                            try:
                                parent.write(block)
                                parent.flush()
                            except Exception as error:
                                errors.append(channel + '_forward: ' + repr(error))
                                parent_ok = False
                    offset += len(block)
            except Exception as error:
                with lock:
                    errors.append(channel + '_read: ' + repr(error))
            finally:
                pipe.close()

        threads = [threading.Thread(target=pump, args=(outlog, parents[0], 'stdout')),
                   threading.Thread(target=pump, args=(errlog, parents[1], 'stderr'))]
        started = []
        interrupted = None
        try:
            for thread in threads:
                thread.start()
                started.append(thread)
            child = subprocess.Popen(command, cwd=os.getcwd(), stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                     shell=False, env=dict(os.environ))
            record.update(status='running', child_pid=child.pid, child_command=command)
            ready.set()
            try:
                save_json(record_path, record)
            except Exception as error:
                errors.append('running_metadata: ' + repr(error))
        finally:
            ready.set()
            if child is not None:
                while True:
                    try:
                        code = child.wait()
                        record.update(natural_exit_code=code, observed_child_exit_code=child.returncode)
                        break
                    except KeyboardInterrupt as error:
                        interrupted = repr(error)
                        # No termination API: the parent's owned-tree policy
                        # controls cancellation. Wait the genuine child exit.
                        continue
            for thread in started:
                while thread.is_alive():
                    try:
                        thread.join()
                    except KeyboardInterrupt as error:
                        interrupted = repr(error)
        if child is None:
            raise RuntimeError('Child was not launched')
        for stream in (outlog, errlog, merged, segments):
            try:
                stream.flush()
                os.fsync(stream.fileno())
            except Exception as error:
                errors.append('final_log_fsync: ' + repr(error))
    if interrupted:
        errors.append('dispatcher_interrupted: ' + interrupted)
    record.update(status='child_completed', natural_exit_code=code, observed_child_exit_code=child.returncode,
                  stream_errors=errors, raw_logs={name: snapshot(path) for name, path in
                                               (('stdout', stdout_path), ('stderr', stderr_path),
                                                ('merged', merged_path), ('segments', index_path))})
    return code, errors


def check_frontend_report(path, paths):
    raw = path.read_bytes()
    report = json.loads(raw.decode('utf-8'))
    declarations = validate_report_payload(report, cached=True, reference=paths['declaration_axes'])
    if len(paths['expected_names']) != 194 or not set(paths['expected_names']).issubset(declarations):
        raise ValueError('Complete cached report is missing the original 194 named source declarations')
    return {'path': str(path), 'sha256': hashlib.sha256(raw).hexdigest(), 'report': report,
            'original_named_count': 194, 'original_all_kernel_count': 225,
            'exact_names_and_individual_axiom_closures_match_frozen_baseline': True}


def main():
    call_id = dt.datetime.now(dt.timezone.utc).strftime('%Y%m%dT%H%M%S%fZ') + '_' + str(os.getpid()) + '_' + uuid.uuid4().hex
    calls = owned(HERE / 'calls_real_candidate')
    calls.mkdir(exist_ok=True)
    call_dir = owned(calls / call_id)
    call_dir.mkdir(exist_ok=False)
    record_path = call_dir / 'call.json'
    record = {'schema': 'lakefront309.real-heavy.call.v1', 'mode': MODE, 'started_utc': utc(), 'pid': os.getpid(),
              'cwd': str(canonical(os.getcwd())), 'incoming_argv': sys.argv[1:], 'status': 'preflight',
              'natural_exit_code': None, 'dispatch_return_code': None, 'not_an_acceptance_certificate': True,
              'metadata_heartbeat_budget': 20000000,
              'environment': {key: os.environ[key] for key in IDENTITY_ENV_KEYS if key in os.environ},
              'dispatcher_source': snapshot(Path(__file__)),
              'native_bridge_source': snapshot(HERE / 'DispatchBridge309.cs'),
              'native_bridge_executable': snapshot(HERE / 'DispatchBridge309.exe')}
    lock_path = lock_bytes = None
    child_code = None
    result = 64
    try:
        save_json(record_path, record)
        configured_policy = os.environ.get('LAKEFRONT309_BRIDGE_POLICY')
        if not configured_policy:
            raise ValueError('The actual native bridge must supply LAKEFRONT309_BRIDGE_POLICY')
        policy_path = owned(absolute_path(configured_policy, regular=True))
        # The launcher/actual bridge validate the policy schema and dispatcher
        # hash before execution. This child binds the dedicated real policy bytes
        # through its genuine child exit; it does not invent another bridge schema.
        record['native_bridge_policy'] = snapshot(policy_path)
        config_path, config_raw, config, paths = load_config()
        stock, selected_driver = paths['stock'], paths['driver']
        record.update(config_path=str(config_path), config_sha256=hashlib.sha256(config_raw).hexdigest(),
                      selected_driver_path=str(selected_driver), original_lean=snapshot(stock),
                      configured_sysroot=str(paths['sysroot']), frontend_driver=snapshot(selected_driver),
                      baseline_evidence={'report': snapshot(paths['baseline_report']),
                                         'request': snapshot(paths['baseline_request'])})
        argv, target = sys.argv[1:], config['target']
        special = observes_heavy(argv, target)
        record['route'] = 'frozen_cached_sequential_frontend' if special else 'stock_lean_original_argv'
        bound = {'source': paths['source'], 'setup': paths['setup'], 'driver': selected_driver, 'stock': stock,
                 'config': config_path, 'dispatcher': Path(__file__), 'baseline_report': paths['baseline_report'],
                 'baseline_request': paths['baseline_request'], 'bridge_source': HERE / 'DispatchBridge309.cs',
                 'bridge_executable': HERE / 'DispatchBridge309.exe', 'bridge_policy': policy_path}
        if special:
            if canonical(os.getcwd()) != paths['cwd']:
                raise ValueError('Heavy compilation cwd must be the exact configured portable package workspace')
            binding = parse_heavy(argv, target, paths)
            record['heavy_binding'] = binding
            locks = owned(HERE / 'locks_real_candidate')
            locks.mkdir(exist_ok=True)
            lock_path = owned(locks / (SOURCE_SHA256 + '.lock'))
            lock_bytes = json.dumps({'pid': os.getpid(), 'call_id': call_id, 'utc': utc()}).encode('utf-8')
            with lock_path.open('xb') as stream:
                stream.write(lock_bytes)
                stream.flush()
                os.fsync(stream.fileno())
            request_path = call_dir / 'frontend.request.json'
            request, report_path, provisional_path = materialize_request(config['request_template'], paths, call_dir)
            save_json(request_path, request)
            record.update(frontend_request=snapshot(request_path), frontend_request_body=request,
                          frontend_request_driver_path=str(selected_driver),
                          provisional_olean_path=str(provisional_path))
            command = frontend_command(stock, selected_driver, request_path)
            bound['request'] = request_path
        else:
            command = [str(stock), *argv]
            record['observed_stock_paths_before'] = {key: snapshot(path) for key, path in observe_stock_paths(argv).items()}
        if configured_driver(config['driver_path']) != selected_driver:
            raise ValueError('Configured cached driver canonical path changed before child launch')
        if (absolute_path(config['stock_lean'], regular=True) != stock
                or absolute_path(config['sysroot'], directory=True) != paths['sysroot']):
            raise ValueError('Configured original Lean/sysroot canonical path changed before child launch')
        record['bound_inputs_before'] = {key: snapshot(path) for key, path in bound.items()}
        expected_bindings = {'source': SOURCE_SHA256, 'setup': target['setup_sha256'],
            'stock': STOCK_SHA256, 'driver': DRIVER_SHA256, 'config': hashlib.sha256(config_raw).hexdigest(),
            'dispatcher': record['dispatcher_source'].get('sha256'),
            'baseline_report': BASELINE_REPORT_SHA256, 'baseline_request': BASELINE_REQUEST_SHA256,
            'bridge_source': record['native_bridge_source'].get('sha256'),
            'bridge_executable': record['native_bridge_executable'].get('sha256'),
            'bridge_policy': record['native_bridge_policy'].get('sha256')}
        if special:
            expected_bindings['request'] = record['frontend_request']['sha256']
        record['expected_input_sha256'] = expected_bindings
        for key, expected in expected_bindings.items():
            if not valid_sha(expected) or record['bound_inputs_before'][key].get('sha256') != expected:
                raise ValueError('Frozen input missing or changed before child launch: ' + key)
        save_json(record_path, record)
        child_code, stream_errors = tee_child(command, call_dir, record, record_path)
        record['raw_log_gate'] = scan_raw_logs(record['raw_logs'])
        raw_errors = record['raw_log_gate']['scan_errors'] + [
            'Fatal raw diagnostic ' + hit['kind'] + ' in ' + hit['stream'] +
            ' at byte ' + str(hit['byte_offset']) + ': ' + hit['matched_text']
            for hit in record['raw_log_gate']['fatal_matches']]
        if raw_errors:
            safe_stderr('lakefront309 real cached raw log contract rejected: ' + '; '.join(raw_errors))
        record['bound_inputs_after'] = {key: snapshot(path) for key, path in bound.items()}
        changed = record['bound_inputs_before'] != record['bound_inputs_after']
        record['bound_inputs_changed'] = changed
        validation_errors = list(stream_errors) + raw_errors
        if changed:
            validation_errors.append('Frozen source/setup/driver/stock/config/request/dispatcher/baseline/actual-bridge bytes changed during this call')
        if special:
            record['output_artifacts'] = {key: snapshot(path) for key, path in paths['artifacts'].items()}
            provisional_outputs = {'olean': provisional_path,
                'ilean': provisional_path.with_name(provisional_path.name + '.ilean'),
                'c': provisional_path.with_name(provisional_path.name + '.c')}
            record['genuine_provisional_artifacts'] = {key: snapshot(path) for key, path in provisional_outputs.items()}
            if child_code == 0:
                try:
                    record['frontend_result'] = check_frontend_report(report_path, paths)
                    for key, final in record['output_artifacts'].items():
                        provisional = record['genuine_provisional_artifacts'][key]
                        if (not final['exists'] or not provisional['exists'] or final['sha256'] != provisional['sha256']
                                or final['bytes'] != provisional['bytes']):
                            raise ValueError('Exit 0 without byte-identical genuine provisional/final artifact: ' + key)
                except Exception as error:
                    validation_errors.append(repr(error))
        else:
            record['observed_stock_paths_after'] = {key: snapshot(path) for key, path in observe_stock_paths(argv).items()}
        result = dispatch_code(child_code, bool(validation_errors), 65)
        record.update(status='completed' if not validation_errors else 'rejected_after_child',
                      validation_errors=validation_errors, dispatch_return_code=result)
    except BaseException as error:
        if child_code is None:
            child_code = record.get('natural_exit_code')
        result = dispatch_code(child_code, True, 64)
        record.update(status='dispatcher_failure', dispatcher_error=repr(error), dispatch_return_code=result)
        safe_stderr('lakefront309 real cached dispatcher failure: ' + repr(error))
    finally:
        if lock_path is not None and lock_bytes is not None:
            try:
                if lock_path.read_bytes() == lock_bytes:
                    lock_path.unlink()
            except FileNotFoundError:
                pass
            except Exception as error:
                record['lock_cleanup_error'] = repr(error)
                if result == 0:
                    result = 65
        flush_errors = []
        for stream in (sys.stdout, sys.stderr):
            try:
                if stream is not None:
                    stream.flush()
            except Exception as error:
                flush_errors.append(repr(error))
        if flush_errors:
            record['parent_stream_flush_errors'] = flush_errors
            if result == 0:
                result = 65
        record.update(ended_utc=utc(), dispatch_return_code=result)
        try:
            save_json(record_path, record)
        except Exception as error:
            safe_stderr('lakefront309 real cached final sidecar failure: ' + repr(error))
            if result == 0:
                result = 65
    return result


if __name__ == '__main__':
    code = main()
    # sys.exit on Windows may narrow or reinterpret unusual exit values.
    # Preserve an observed Windows DWORD explicitly after flushing streams.
    if os.name == 'nt':
        import ctypes
        kernel = ctypes.WinDLL('kernel32', use_last_error=True)
        kernel.ExitProcess.argtypes = [ctypes.c_uint32]
        kernel.ExitProcess.restype = None
        kernel.ExitProcess(code & 0xFFFFFFFF)
    raise SystemExit(code)
