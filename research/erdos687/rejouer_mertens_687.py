"""Replay the Mertens estimate from the accepted Left to Solve proof."""
import argparse
import hashlib
from pathlib import Path
from urllib.request import urlopen


REVISION = "8ac3e8d3d7c3356672d73d554849424def57e6b7"
URL = ("https://raw.githubusercontent.com/GuillaumeBAUD-coder/open-math-agents/"
       + REVISION + "/proofs/Erdos687.erdos_687.variants.iwaniec.R1.H2.lean")
DIGEST = "ed95c60562429b3a14e0bb714599b11b3a28cc8e1c102e73aa03ec011a89f104"


def make_module(source):
    if source:
        data = source.read_bytes()
    else:
        with urlopen(URL, timeout=45) as response:
            data = response.read()
    if hashlib.sha256(data).hexdigest() != DIGEST:
        raise ValueError("Unexpected digest for the published Mertens proof")
    text = data.decode("utf-8")
    # The discarded catalog wrapper merely applies the main theorem at n >= 3
    # and verifies n = 2. Preserve the proof and its attribution.
    text = text[text.index("import Mathlib"):text.index("theorem OMA.solution")]
    return "-- From the accepted proof at " + URL + "\n" + text


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("output", type=Path)
    parser.add_argument("--source", type=Path)
    args = parser.parse_args()
    args.output.write_text(make_module(args.source), encoding="utf-8")
