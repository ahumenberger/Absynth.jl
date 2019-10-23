using PyCall

deps_pip = ["z3-solver", "pysmt"]
run(`$(PyCall.pyprogramname) -m pip install -- $deps_pip`)