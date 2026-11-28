"""Check an assembled wheel in Lean, reusing matching audited group outputs."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys


def digest(path):
    with path.open("rb") as source:
        return hashlib.file_digest(source, "sha256").hexdigest()


def check(directory, wheel, memory):
    manifest = directory / (wheel + "Full.lean")
    groups = re.findall(r"^(?:public )?import (" + re.escape(wheel) + r"Group\d+)$",
                        manifest.read_text(encoding="utf-8"), re.MULTILINE)
    if not groups or len(groups) != len(set(groups)):
        raise ValueError("Missing or repeated groups in the assembled proof")
    env = os.environ.copy()
    env["LEAN_PATH"] = os.pathsep.join(filter(None, [str(directory), env.get("LEAN_PATH")]))
    version = subprocess.check_output(["lean", "--version"], text=True).strip()
    sources = Path(__file__).resolve().parent
    temporary_dir = directory / "checking"
    temporary_dir.mkdir(exist_ok=True)

    def public_data(name):
        # Migrate already generated numeric inputs. Only the theorem is
        # needed by later groups, so the large weight words stay private.
        path = directory / (name + ".lean")
        with path.open(encoding="utf-8") as stream:
            if stream.readline().strip() == "module":
                return
        source = path.read_text(encoding="utf-8")
        source = re.sub(r"^import ", "public import ", source, flags=re.MULTILINE)
        if name == wheel:
            source = source.replace("namespace " + wheel, "@[expose] public section\nnamespace " + wheel, 1)
        else:
            source = source.replace("\ntheorem certified :", "\npublic theorem certified :")
        temporary = path.with_suffix(".lean.tmp")
        temporary.write_text("module\n" + source, encoding="utf-8")
        temporary.replace(path)

    def compile_module(name, audit=False):
        source = directory / (name + ".lean")
        log = directory / (name + ".log")
        output = directory / (name + ".olean")
        temporary = temporary_dir / (name + ".olean")
        with log.open("wb") as diagnostics:
            result = subprocess.run(["lean", "-j1", "-M", str(memory), "-o", str(temporary), source.name],
                                    cwd=directory, env=env, stdout=diagnostics, stderr=subprocess.STDOUT)
        report = log.read_text(encoding="utf-8", errors="replace")
        if result.returncode:
            raise RuntimeError(f"{name}: {report[-1600:]}")
        if audit:
            allowed = {"propext", "Classical.choice", "Quot.sound"}
            match = re.search(r"depends on axioms:\s*\[([^\]]*)\]", report)
            independent = "does not depend on any axioms" in report
            if not independent and (not match or
                    any(a.strip() not in allowed for a in match[1].split(",") if a.strip())):
                raise RuntimeError(f"Unexpected axiom report for {name}: {report[-1200:]}")
        for extension in [".ir", ".ir.sig"]:
            code = temporary_dir / (name + extension)
            if code.exists():
                code.replace(directory / code.name)
        for extension in [".private", ".server", ""]:
            artifact = Path(str(temporary) + extension)
            if artifact.exists():
                artifact.replace(Path(str(output) + extension))
        return output

    # The concrete data checks are independent of Mathlib. Compile the small
    # interpreting modules here so their identities are part of each receipt.
    def compile_supplied(name):
        original = sources / (name + ".lean")
        target = directory / (name + ".lean")
        if original != target:
            target.write_bytes(original.read_bytes())
        compile_module(name)
    for name in ["VerificationPoids687", "Branches19_687", "EntierPoids687"]:
        compile_supplied(name)
    public_data(wheel)
    compile_module(wheel)
    for name in ["PolynomePoids687", "NoyauPondere687", "Phases687"]:
        compile_supplied(name)
    x, h = re.fullmatch(r"Wheel(\d+)H(\d+)", wheel).groups()
    compile_module("ListePremiers" + wheel)
    compile_module(f"Critere{x}H{h}", audit=True)
    parents = [digest(directory / (name + ".olean")) for name in
               ["VerificationPoids687", "Branches19_687", wheel]]
    for index, name in enumerate(groups, 1):
        public_data(name)
        source = directory / (name + ".lean")
        output = directory / (name + ".olean")
        receipt = directory / (name + ".audit.json")
        signature = [version, *parents, digest(source)]
        previous = json.loads(receipt.read_text()) if receipt.is_file() else {}
        def outputs():
            return [digest(p) if p.is_file() else None for p in
                    (output, Path(str(output)+".private"), Path(str(output)+".server"))]
        if previous.get("inputs") != signature or not output.is_file() or previous.get("outputs") != outputs():
            compile_module(name, audit=True)
            record = {"inputs": signature, "outputs": outputs()}
            temporary = receipt.with_suffix(".tmp")
            temporary.write_text(json.dumps(record), encoding="utf-8")
            temporary.replace(receipt)
        if index == 1 or index % 10 == 0 or index == len(groups):
            print(f"{index}/{len(groups)} verified", flush=True)
    public_data(wheel + "Full")
    compile_module(wheel + "Full", audit=True)
    final = f"Borne{x}H{h}"
    compile_module(final, audit=True)
    print((directory / (final + ".log")).read_text(encoding="utf-8"), flush=True)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("directory", type=Path)
    parser.add_argument("wheel", help="the mixed-wheel module, for example Wheel1223H11850")
    parser.add_argument("--memory", type=int, default=4000, help="Lean memory limit in MiB per process")
    args = parser.parse_args()
    try:
        check(args.directory.resolve(), args.wheel, args.memory)
    except (RuntimeError, ValueError, OSError) as error:
        sys.exit(str(error))
