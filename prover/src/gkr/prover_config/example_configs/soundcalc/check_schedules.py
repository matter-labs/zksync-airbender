"""Certify serialized Rust schedules with soundcalc 2af5e7d."""
import json
import sys

import l1_wrap
import whir_schedule_search as search


def main():
    data = json.load(sys.stdin)
    for entry in data["baby_bear"]:
        levels = search.certify_baby_bear(
            entry["schedule"], entry["message_log2"], entry["columns"], entry["multiplicities"],
        )
        minimum = min(levels.values())
        assert minimum == levels[entry["binding_term"]] == entry["certified_bits"], levels
        print(json.dumps(dict(shape=entry["shape"], minimum=minimum, levels=levels)))

    wrap = data["l1_wrap"]
    m = wrap["base_soundness"]["Ethproofs"]["JohnsonBound"]["m"]
    assert m == 3, "L1 wrap uses the Johnson bound with multiplicity 3"
    certificate = l1_wrap.certify(wrap["whir_schedule"], wrap["trace_len_log2"], 14, 2**128 / 37)
    print(json.dumps(dict(shape="L1 wrap", minimum=min(certificate["levels"].values()), **certificate)))


if __name__ == "__main__":
    main()
