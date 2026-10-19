#!/usr/bin/env python3
"""Install the pinned Lean toolchain before lean-action runs elan.

elan downloads a toolchain during the first `lean --version` and retries that
download only once, so one TLS failure fails the CI job. This script retries
the release asset with exponential backoff, verifies its SHA-256, and installs
it where elan looks, so elan finds the toolchain already present. Toolchains
or platforms without a pinned entry are skipped and lean-action downloads them.
"""
import hashlib
import http.client
import os
import platform
import re
import shutil
import subprocess
import sys
import tempfile
import time
import urllib.request
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
ATTEMPTS = 6
FIRST_BACKOFF = 15  # seconds; doubles after each failed attempt
TIMEOUT = 120  # seconds per socket operation
CHUNK = 1 << 20
MIRRORS = ("https://github.com/leanprover/lean4/releases/download/{tag}/{asset}",
           "https://releases.lean-lang.org/lean4/{tag}/{asset}")

# Toolchain -> platform -> (release asset, size in bytes, SHA-256).
# A toolchain bump edits lean-toolchain and this one entry.
PINNED = {
    "leanprover/lean4:v4.32.0": {"linux-x86_64": ("lean-4.32.0-linux.tar.zst", 559392068, "fca846f3588724a38ad19ee40292c67cb7438d7555903372e3308eef795ba516")},
}


def parse_toolchain(text):
    """Return the release tag, such as v4.32.0, named by a lean-toolchain line, or None."""
    match = re.fullmatch(r"leanprover/lean4:(v\d+\.\d+\.\d+)", text.strip())
    return match.group(1) if match else None


def toolchain_dir_name(text):
    """Return elan's directory name for a toolchain, such as leanprover--lean4---v4.32.0."""
    return text.strip().replace("/", "--").replace(":", "---")


def platform_key():
    return f"{platform.system().lower()}-{platform.machine()}"


def sha256_of(path):
    digest = hashlib.sha256()
    with open(path, "rb") as stream:
        for block in iter(lambda: stream.read(CHUNK), b""):
            digest.update(block)
    return digest.hexdigest()


def verify_sha256(path, expected):
    actual = sha256_of(path)
    if actual != expected:
        raise ValueError(f"{path.name}: SHA-256 {actual} does not match {expected}")


def download_once(url, dest, size):
    """Stream url into dest. A short body raises OSError so that the attempt is retried."""
    with urllib.request.urlopen(url, timeout=TIMEOUT) as response, open(dest, "wb") as out:
        shutil.copyfileobj(response, out, CHUNK)
    got = dest.stat().st_size
    if got != size:
        raise OSError(f"got {got} bytes, expected {size}")


def fetch(tag, asset, size, dest, sleep=time.sleep):
    """Try GitHub, then the mirror, in each of ATTEMPTS attempts; back off between attempts."""
    delay = FIRST_BACKOFF
    for attempt in range(1, ATTEMPTS + 1):
        for template in MIRRORS:
            url = template.format(tag=tag, asset=asset)
            try:
                download_once(url, dest, size)
                return url
            except (OSError, http.client.HTTPException) as error:
                print(f"attempt {attempt}/{ATTEMPTS} failed for {url}: {error}", file=sys.stderr)
        if attempt < ATTEMPTS:
            print(f"retrying in {delay} s", file=sys.stderr)
            sleep(delay)
            delay *= 2
    raise OSError(f"all {ATTEMPTS} download attempts failed for {asset}")


def install(root=ROOT, elan_home=None):
    """Install the toolchain that root/lean-toolchain names; return the exit code."""
    text = (root / "lean-toolchain").read_text().strip()
    tag = parse_toolchain(text)
    key = platform_key()
    entry = PINNED.get(text, {}).get(key)
    if tag is None or entry is None:
        print(f"prefetch_toolchain: no pinned download for {text!r} on {key}; lean-action will download it")
        return 0
    elan_home = Path(elan_home or os.environ.get("ELAN_HOME") or Path.home() / ".elan")
    toolchains = elan_home / "toolchains"
    target = toolchains / toolchain_dir_name(text)
    if target.exists():
        print(f"prefetch_toolchain: {target} already exists")
        return 0
    asset, size, sha256 = entry
    toolchains.mkdir(parents=True, exist_ok=True)
    # The staging directory sits under elan_home, so the final rename stays on one filesystem.
    with tempfile.TemporaryDirectory(prefix="lean-prefetch-", dir=elan_home) as work:
        archive = Path(work) / asset
        url = fetch(tag, asset, size, archive)
        print(f"prefetch_toolchain: downloaded {asset} from {url}")
        verify_sha256(archive, sha256)
        extract = Path(work) / "extract"
        extract.mkdir()
        subprocess.run(["tar", "--use-compress-program=unzstd", "-xf", str(archive), "-C", str(extract)], check=True)
        top = extract / asset.removesuffix(".tar.zst")
        if not top.is_dir():
            raise ValueError(f"{asset} does not contain {top.name}/")
        os.rename(top, target)
    print(f"prefetch_toolchain: installed {target}")
    return 0


def main():
    try:
        return install()
    except (OSError, ValueError, subprocess.CalledProcessError) as error:
        print(f"prefetch_toolchain: FAIL: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())
