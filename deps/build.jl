deps_pip = ["z3-solver", "yices"]

run(`$(PyCall.pyprogramname) -m pip install -- $(join(deps_pip, " "))`)