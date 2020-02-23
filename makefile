.PHONY: help
help:
	cat makefile

.PHONY: clean
clean:
	bash -ci "ac 3; python setup.py clean"
	rm -rf build .pytest_cache
	find * -name '*.pyc' -delete
	find * -name __pycache__ -delete

.PHONY: build
build:
	bash -ci "ac 3; python setup.py build"

.PHONY: install
install: build
	bash -ci "ac 3; python setup.py install"

.PHONY: test
test: install
	bash -ci "ac 3; pytest -v -s tests"
