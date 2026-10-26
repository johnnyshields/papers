#!/usr/bin/env python3
"""Spool a subprocess log on local scratch and publish retrying atomic snapshots."""
import argparse
import os
from pathlib import Path
import subprocess
import time


def publish(path, data):
    for attempt in range(9):
        try:
            path.parent.mkdir(parents=True, exist_ok=True)
            temporary = path.with_suffix(path.suffix + '.tmp')
            with temporary.open('wb') as stream:
                stream.write(data)
                stream.flush()
                os.fsync(stream.fileno())
            os.replace(temporary, path)
            return True
        except OSError:
            time.sleep(min(2 ** attempt, 30))
    # The hot log remains authoritative until a later successful publication.
    return False


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--log', type=Path, required=True)
    parser.add_argument('--hot-log', type=Path, required=True)
    parser.add_argument('command', nargs=argparse.REMAINDER)
    args = parser.parse_args()
    command = args.command
    if command[0] == '--':
        command = command[1:]
    args.hot_log.parent.mkdir(parents=True, exist_ok=True)
    log = bytearray()
    with args.hot_log.open('wb') as hot:
        with subprocess.Popen(command, stdout=subprocess.PIPE, stderr=subprocess.STDOUT) as child:
            for line in iter(child.stdout.readline, b''):
                hot.write(line)
                hot.flush()
                log.extend(line)
                publish(args.log, log)
            returncode = child.wait()
        hot.flush()
        os.fsync(hot.fileno())
    publish(args.log, log)
    raise SystemExit(returncode)


if __name__ == '__main__':
    main()
