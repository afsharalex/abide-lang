#!/usr/bin/env python3

from __future__ import annotations

import argparse
import os
import signal
import subprocess
import sys
import time
from collections import defaultdict
from pathlib import Path


DEFAULT_TIMEOUT_SECS = 3600
DEFAULT_GRACE_SECS = 5


def _read_process_table() -> dict[int, list[int]]:
    children: dict[int, list[int]] = defaultdict(list)
    try:
        proc = subprocess.run(
            ["ps", "-Ao", "pid=,ppid="],
            text=True,
            capture_output=True,
            check=False,
        )
    except OSError:
        return children
    for line in proc.stdout.splitlines():
        parts = line.split()
        if len(parts) != 2:
            continue
        try:
            pid = int(parts[0])
            ppid = int(parts[1])
        except ValueError:
            continue
        children[ppid].append(pid)
    return children


def _descendant_pids(root_pid: int) -> list[int]:
    children = _read_process_table()
    descendants: list[int] = []
    stack = list(children.get(root_pid, []))
    while stack:
        pid = stack.pop()
        descendants.append(pid)
        stack.extend(children.get(pid, []))
    return descendants


def _signal_processes(proc: subprocess.Popen, sig: int) -> None:
    current_pid = os.getpid()
    for pid in reversed(_descendant_pids(proc.pid)):
        if pid == current_pid:
            continue
        try:
            os.kill(pid, sig)
        except ProcessLookupError:
            pass
    if os.name == "posix":
        try:
            os.killpg(os.getpgid(proc.pid), sig)
            return
        except ProcessLookupError:
            return
        except OSError:
            pass
    try:
        proc.send_signal(sig)
    except ProcessLookupError:
        pass


def _terminate_tree(proc: subprocess.Popen, grace_secs: int) -> None:
    if proc.poll() is not None:
        return
    _signal_processes(proc, signal.SIGTERM)
    deadline = time.monotonic() + max(grace_secs, 0)
    while proc.poll() is None and time.monotonic() < deadline:
        time.sleep(0.1)
    if proc.poll() is None:
        _signal_processes(proc, signal.SIGKILL)
        proc.wait()


def _timeout_from_env() -> int:
    for key in ("ABIDE_PROCESS_TIMEOUT_SECS", "ABIDE_CARGO_TIMEOUT_SECS"):
        value = os.environ.get(key)
        if value:
            try:
                return int(value)
            except ValueError:
                pass
    return DEFAULT_TIMEOUT_SECS


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Run a command with a process-tree timeout."
    )
    parser.add_argument(
        "--timeout-secs",
        type=int,
        default=_timeout_from_env(),
        help="timeout in seconds; 0 disables the timeout",
    )
    parser.add_argument(
        "--grace-secs",
        type=int,
        default=DEFAULT_GRACE_SECS,
        help="seconds to wait after SIGTERM before SIGKILL",
    )
    parser.add_argument("--cwd", type=Path, help="working directory for the command")
    parser.add_argument("--label", help="human-readable command label")
    parser.add_argument("cmd", nargs=argparse.REMAINDER)
    args = parser.parse_args()
    if args.cmd and args.cmd[0] == "--":
        args.cmd = args.cmd[1:]
    if not args.cmd:
        parser.error("missing command after --")
    return args


def main() -> int:
    args = parse_args()
    label = args.label or " ".join(args.cmd)
    start_new_session = os.name == "posix"
    proc = subprocess.Popen(
        args.cmd,
        cwd=args.cwd,
        start_new_session=start_new_session,
    )
    deadline = (
        time.monotonic() + args.timeout_secs if args.timeout_secs and args.timeout_secs > 0 else None
    )
    try:
        while True:
            returncode = proc.poll()
            if returncode is not None:
                return returncode
            if deadline is not None and time.monotonic() >= deadline:
                print(
                    f"{label} timed out after {args.timeout_secs} seconds; terminating process tree",
                    file=sys.stderr,
                )
                _terminate_tree(proc, args.grace_secs)
                return 124
            time.sleep(0.2)
    except KeyboardInterrupt:
        print(f"{label} interrupted; terminating process tree", file=sys.stderr)
        _terminate_tree(proc, args.grace_secs)
        return 130


if __name__ == "__main__":
    raise SystemExit(main())
