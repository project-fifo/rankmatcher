REBAR=./rebar
.phony: all test

all:
	$(REBAR) compile

test:
	$(REBAR) eunit
