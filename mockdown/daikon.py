from textwrap import dedent, indent
from typing import List

from .constrainable import ConstrainablePair
from .view import View


def decls_header(name: str) -> str:
    return dedent(f"""\
        decl-version 2.0
        input-language data
        
        ppt {name}.data:::POINT
        ppt-type point
    """)


def decls_variable(name: str, dec_type: str, rep_type: str = "int", comparability: int = 0):
    return indent(dedent(f"""\
        variable {name}
          var-kind variable
          dec-type {dec_type}
          rep-type {rep_type}
          comparability {comparability}
    """), "  ")


def generate_decls(name: str, view: View, constrainable_pairs: List[ConstrainablePair]) -> str:
    output = [decls_header(name)]

    ck = 0
    for pair in constrainable_pairs:
        for anchor in [pair.anchor1, pair.anchor2]:
            variable = decls_variable(f"{anchor.name}_{ck}", pair.kind, comparability=ck)
            output.append(variable)
        ck += 1

    return ''.join(output)


def dtrace_header(name: str) -> str:
    return dedent(f"""\
        {name}.data:::POINT
    """).rstrip()


def dtrace_trace(name: str, value: int) -> str:
    return dedent(f"""
        {name}
        {value}
        1
    """).rstrip()


def generate_dtrace(name: str, view: View, constrainable_pairs: List[ConstrainablePair]) -> str:
    output = [dtrace_header(name)]

    ck = 0
    for pair in constrainable_pairs:
        for anchor in [pair.anchor1, pair.anchor2]:
            variable = dtrace_trace(f"{anchor.name}_{ck}", anchor.value)
            output.append(variable)
        ck += 1

    return ''.join(output)
