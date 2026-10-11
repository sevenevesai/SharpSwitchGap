"""Verify the vendored upstream Lean files against the pinned openai/math commit.

Run from any directory:
    python verify_vendor.py                  offline: manifest hashes, import closure, Comparator match
    python verify_vendor.py --fetch          also download every manifest entry from GitHub at the pin
    python verify_vendor.py --checkout DIR   also compare the manifest with `git ls-tree` in a local
                                             clone of openai/math that contains the pinned commit

Success prints PASS lines and exits 0. The first mismatch raises an error.

vendor/MANIFEST.txt lists one file per line as `<git blob sha1>\t<path in openai/math>`.
A path `lean/X` is stored at `vendor/X`; `LICENSE` is stored at `vendor/LICENSE`.
"""

from __future__ import annotations

import argparse
import hashlib
import re
import subprocess
import urllib.request
from pathlib import Path

PIN = "adc7f1241b42e322a6451854ab7e4b4c146bf78a"
HERE = Path(__file__).resolve().parent
VENDOR = HERE / "vendor"
MANIFEST = VENDOR / "MANIFEST.txt"
MAIN = "OAI.Probability.SwitchChain.Main"
COMPARATOR = "lean/ComparatorChallenges/SwitchChain.lean"
THEOREMS = ("switch_chain_main", "switch_chain_tv_bound", "switch_connectivity")
RAW = f"https://raw.githubusercontent.com/openai/math/{PIN}/"


def blob_hash(data: bytes) -> str:
    return hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()


def compact(text: str) -> str:
    return re.sub(r"\s+", "", text)


def imports(text: str) -> list[str]:
    # The pinned files use one plain, unquoted import per line. Fail closed on any other
    # syntax rather than computing an incomplete import graph.
    result = []
    for line in text.splitlines():
        if line.startswith("import "):
            match = re.fullmatch(r"import ([A-Za-z0-9_.]+)\s*", line)
            if match is None:
                raise ValueError(f"Unsupported import: {line}")
            result.append(match[1])
    return result


def statement(text: str, name: str) -> str:
    match = re.search(r"theorem " + name + r"\s*:\s*(.*?)\s*:=\s*by", text, re.S)
    if match is None:
        raise ValueError(f"Missing theorem statement: {name}")
    return compact(match[1])


def local_path(upstream: str) -> Path:
    return VENDOR / (upstream[len("lean/"):] if upstream.startswith("lean/") else upstream)


def read_manifest() -> dict[str, str]:
    manifest: dict[str, str] = {}
    for line in MANIFEST.read_text(encoding="utf-8").splitlines():
        if not line.strip():
            continue
        digest, upstream = line.split("\t", 1)
        manifest[upstream] = digest
    return manifest


def check_hashes(manifest: dict[str, str]) -> None:
    converted = 0
    for upstream, digest in manifest.items():
        data = local_path(upstream).read_bytes()
        if blob_hash(data) != digest and blob_hash(data.replace(b"\r\n", b"\n")) == digest:
            # A checkout with CRLF conversion; the content is still the pinned blob.
            converted += 1
            continue
        if blob_hash(data) != digest:
            raise ValueError(f"Blob hash mismatch: {upstream}")
    if converted:
        print(f"note: {converted} files carry CRLF line endings from checkout; hashes match after conversion")
    listed = {local_path(u).resolve() for u in manifest} | {MANIFEST.resolve()}
    for path in VENDOR.rglob("*"):
        if path.is_file() and path.resolve() not in listed:
            raise ValueError(f"File under vendor/ is not in the manifest: {path}")
    print(f"PASS: {len(manifest)} vendored files match their pinned Git blob hashes")


def check_closure(manifest: dict[str, str]) -> dict[str, str]:
    todo = [MAIN]
    for own in (HERE / "SharpSwitchGap").rglob("*.lean"):
        todo.extend(i for i in imports(own.read_text(encoding="utf-8")) if i.startswith("OAI."))
    modules: dict[str, str] = {}
    external: set[str] = set()
    while todo:
        name = todo.pop()
        if name in modules:
            continue
        upstream = "lean/" + name.replace(".", "/") + ".lean"
        if upstream not in manifest:
            raise ValueError(f"Imported upstream module is not vendored: {name}")
        text = local_path(upstream).read_text(encoding="utf-8")
        modules[name] = text
        for dependency in imports(text):
            if dependency.startswith("OAI."):
                todo.append(dependency)
            else:
                external.add(dependency)
    if external != {"Mathlib"}:
        raise ValueError(f"Unexpected external imports: {sorted(external)}")
    unused = sorted(
        u for u in manifest
        if u.startswith("lean/OAI/") and u[len("lean/"):-len(".lean")].replace("/", ".") not in modules
    )
    if unused:
        raise ValueError(f"Vendored modules outside the import closure: {unused}")
    print(f"PASS: import closure of {len(modules)} OAI modules; external imports {sorted(external)}")
    return modules


def check_comparator(modules: dict[str, str]) -> None:
    comparator = local_path(COMPARATOR).read_text(encoding="utf-8")
    definitions = modules["OAI.Probability.SwitchChain.Definitions"]
    main_text = modules[MAIN]
    expected = comparator[comparator.index("def graphDegree"):comparator.index("\ntheorem switch_chain_main")]
    actual = definitions[definitions.index("def graphDegree"):definitions.index("\nend Problem315")]
    if compact(expected) != compact(actual):
        raise ValueError("Comparator definitions differ from the pinned Definitions module")
    for name in THEOREMS:
        if statement(comparator, name) != statement(main_text, name):
            raise ValueError(f"Comparator statement differs: {name}")
    print("PASS: Comparator definitions and all three theorem types match (whitespace normalized)")


def check_fetch(manifest: dict[str, str]) -> None:
    for upstream, digest in manifest.items():
        with urllib.request.urlopen(RAW + upstream) as response:
            data = response.read()
        if blob_hash(data) != digest:
            raise ValueError(f"Upstream file differs from the manifest: {upstream}")
    print(f"PASS: {len(manifest)} files re-downloaded from openai/math at {PIN[:7]} match the manifest")


def check_checkout(manifest: dict[str, str], checkout: Path) -> None:
    def git(*args: str) -> str:
        return subprocess.check_output(["git", "-C", str(checkout), *args], encoding="utf-8").strip()

    git("cat-file", "-e", PIN + "^{commit}")
    tree: dict[str, str] = {}
    for line in git("ls-tree", "-r", PIN, "--", *sorted(manifest)).splitlines():
        meta, path = line.split("\t", 1)
        tree[path] = meta.split()[2]
    for upstream, digest in manifest.items():
        if tree.get(upstream) != digest:
            raise ValueError(f"Manifest entry differs from the pinned tree: {upstream}")
    print(f"PASS: manifest matches `git ls-tree {PIN[:7]}` in {checkout}")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--fetch", action="store_true", help="re-download each file from GitHub at the pin")
    parser.add_argument("--checkout", type=Path, help="local clone of openai/math containing the pin")
    args = parser.parse_args()
    manifest = read_manifest()
    check_hashes(manifest)
    modules = check_closure(manifest)
    check_comparator(modules)
    if args.fetch:
        check_fetch(manifest)
    if args.checkout:
        check_checkout(manifest, args.checkout)


if __name__ == "__main__":
    main()
