using PyCall

deps_pip = ["pysmt"]
run(`$(PyCall.pyprogramname) -m pip install -- $deps_pip`)