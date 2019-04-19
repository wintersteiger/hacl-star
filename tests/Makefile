all: .gen-tests

.PRECIOUS: .gen-tests
.gen-tests:
	mkdir -p generated/json
	python3 gen_json_SHA3.py
	python3 gen_json_Chacha20Poly1305.py
	touch .gen-tests

clean:
	rm -rf generated .gen-tests
