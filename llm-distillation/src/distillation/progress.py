"""Grey one-line progress readout: `[1/9] CooperateBot 5/30 calls | 1m02s, ETA 3m10s`."""

import os
import sys
import time

if os.name == "nt":
    os.system("")  # enable ANSI escapes on Windows consoles


def _fmt(s: float) -> str:
    m, s = divmod(int(s), 60)
    return f"{m}m{s:02d}s"


class Progress:
    def __init__(self, n_bots: int, n_per_bot: int):
        self.n_bots, self.n_per_bot = n_bots, n_per_bot
        self.start, self.done = time.monotonic(), 0

    def show(self, i: int, bot: str, calls: int) -> None:
        elapsed = time.monotonic() - self.start
        left = self.n_bots * self.n_per_bot - self.done
        eta = _fmt(elapsed / self.done * left) if self.done else "?"
        sys.stderr.write(f"\r\033[2K\033[90m[{i + 1}/{self.n_bots}] {bot} "
                         f"{calls}/{self.n_per_bot} calls | {_fmt(elapsed)}, ETA {eta}\033[0m")
        sys.stderr.flush()

    def clear(self) -> None:
        sys.stderr.write("\r\033[2K")
