#!/usr/bin/env python3
"""Create an immutable, checksummed snapshot of the two chart-finder dependencies."""
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
from cross_check import atomic_json
from run_logged import publish

HERE = Path(__file__).resolve().parent


def main():
    target = HERE / '_pinned'
    target.mkdir(exist_ok=True)
    metadata_path = target / 'snapshot.json'
    if metadata_path.exists():
        metadata = json.loads(metadata_path.read_bytes())
        for name, info in metadata['files'].items():
            assert hashlib.sha256((target / name).read_bytes()).hexdigest() == info['sha256']
        print(json.dumps(metadata, indent=2))
        return
    metadata = dict(captured_utc=datetime.now(timezone.utc).isoformat(), files={})
    for name in ('skew_compose.py', 'skew_core.py'):
        source = HERE.parent / name
        data = source.read_bytes()
        assert data == source.read_bytes(), 'source changed while snapshot was read'
        destination = target / name
        assert not destination.exists(), 'refusing to replace a pinned source file'
        assert publish(destination, data)
        digest = hashlib.sha256(data).hexdigest()
        assert hashlib.sha256(destination.read_bytes()).hexdigest() == digest
        metadata['files'][name] = dict(sha256=digest, bytes=len(data))
    atomic_json(metadata_path, metadata)
    atomic_json(HERE / 'results' / 'finder-snapshot.json', metadata)
    atomic_json(Path('/mnt/d/mvw-rust/finder-snapshot.json'), metadata)
    print(json.dumps(metadata, indent=2))


if __name__ == '__main__':
    main()
