"""Offline checks for the toolchain prefetch: parsing, pinned lookup, skips, retries, and hashes."""
import contextlib
import hashlib
import io
import sys
import tempfile
import unittest
import urllib.error
from pathlib import Path
from unittest.mock import patch

sys.path.insert(0,str(Path(__file__).resolve().parents[1]))
import prefetch_toolchain as pf

PINNED_TOOLCHAIN="leanprover/lean4:v4.32.0"


class ParseTests(unittest.TestCase):
    def test_release_tag_is_parsed(self):
        self.assertEqual(pf.parse_toolchain("leanprover/lean4:v4.32.0\n"),"v4.32.0")

    def test_other_toolchains_are_not_release_tags(self):
        for text in ("leanprover/lean4:v4.34.0-rc1","leanprover/lean4:stable","leanprover/lean4:nightly","other/lean4:v4.32.0"):
            self.assertIsNone(pf.parse_toolchain(text),text)

    def test_elan_directory_name(self):
        self.assertEqual(pf.toolchain_dir_name(PINNED_TOOLCHAIN),"leanprover--lean4---v4.32.0")


class PinnedTableTests(unittest.TestCase):
    def test_checked_in_toolchain_has_full_pinned_metadata(self):
        text=(pf.ROOT/"lean-toolchain").read_text().strip()
        self.assertEqual(text,PINNED_TOOLCHAIN)
        asset,size,sha256=pf.PINNED[text]["linux-x86_64"]
        self.assertEqual(asset,"lean-4.32.0-linux.tar.zst")
        self.assertEqual(size,559392068)
        self.assertRegex(sha256,r"^[0-9a-f]{64}$")

    def test_unpinned_toolchain_has_no_entry(self):
        self.assertIsNone(pf.PINNED.get("leanprover/lean4:v4.33.0"))


class SkipTests(unittest.TestCase):
    def test_unknown_toolchain_exits_zero_without_network(self):
        with tempfile.TemporaryDirectory() as tmp:
            root,elan_home=Path(tmp)/"repo",Path(tmp)/"elan"
            root.mkdir()
            (root/"lean-toolchain").write_text("leanprover/lean4:v4.33.0\n")
            with patch.object(pf.urllib.request,"urlopen",side_effect=AssertionError("network used")), contextlib.redirect_stdout(io.StringIO()):
                self.assertEqual(pf.install(root,elan_home),0)
            self.assertFalse(elan_home.exists())

    def test_existing_toolchain_directory_is_left_alone(self):
        with tempfile.TemporaryDirectory() as tmp:
            root,elan_home=Path(tmp)/"repo",Path(tmp)/"elan"
            root.mkdir()
            (root/"lean-toolchain").write_text(PINNED_TOOLCHAIN+"\n")
            (elan_home/"toolchains"/"leanprover--lean4---v4.32.0").mkdir(parents=True)
            with patch.object(pf,"platform_key",return_value="linux-x86_64"), patch.object(pf.urllib.request,"urlopen",side_effect=AssertionError("network used")), contextlib.redirect_stdout(io.StringIO()):
                self.assertEqual(pf.install(root,elan_home),0)


class HashTests(unittest.TestCase):
    def test_digest_matches_and_mismatch_is_rejected(self):
        payload=b"lean toolchain\n"
        with tempfile.TemporaryDirectory() as tmp:
            path=Path(tmp)/"small.bin"
            path.write_bytes(payload)
            self.assertEqual(pf.sha256_of(path),hashlib.sha256(payload).hexdigest())
            pf.verify_sha256(path,hashlib.sha256(payload).hexdigest())
            with self.assertRaises(ValueError):
                pf.verify_sha256(path,"0"*64)


class FetchTests(unittest.TestCase):
    def test_github_failure_falls_back_to_mirror_in_the_same_attempt(self):
        payload=b"x"*10
        def fake_urlopen(url,timeout):
            if url.startswith("https://github.com/"):
                raise urllib.error.URLError("tls")
            return io.BytesIO(payload)
        with tempfile.TemporaryDirectory() as tmp, patch.object(pf.urllib.request,"urlopen",side_effect=fake_urlopen), contextlib.redirect_stderr(io.StringIO()):
            url=pf.fetch("v4.32.0","a.tar.zst",len(payload),Path(tmp)/"a.tar.zst",sleep=self.fail)
            self.assertTrue(url.startswith("https://releases.lean-lang.org/"))
            self.assertEqual((Path(tmp)/"a.tar.zst").read_bytes(),payload)

    def test_backoff_doubles_and_gives_up_after_six_attempts(self):
        sleeps=[]
        with tempfile.TemporaryDirectory() as tmp, patch.object(pf.urllib.request,"urlopen",side_effect=urllib.error.URLError("tls")) as urlopen, contextlib.redirect_stderr(io.StringIO()):
            with self.assertRaises(OSError):
                pf.fetch("v4.32.0","a.tar.zst",1,Path(tmp)/"a.tar.zst",sleep=sleeps.append)
        self.assertEqual(sleeps,[15,30,60,120,240])
        self.assertEqual(urlopen.call_count,2*pf.ATTEMPTS)


if __name__=="__main__":
    unittest.main()
