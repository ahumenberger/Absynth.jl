using PyCall

deps_pip = ["z3-solver", "yices", "pysmt"]
run(`$(PyCall.pyprogramname) -m pip install -- $deps_pip`)