.PHONY: help
help:
	cat makefile

.PHONY: clean
clean:
	pip uninstall int_str
	rm -rf \
		build \
		dist \
		int_str.egg-info \
		int_str.cpython-310-x86_64-linux-gnu.so \
		.pytest_cache
	# find * -name '*.pyc' -delete
	# find * -name __pycache__ -delete

.PHONY: build
build:
	python -m build

.PHONY: install
install: 
	pip install -e .

.PHONY: test
test: install
	pytest -v -s tests
