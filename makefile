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

dist/int_str-1.0.tar.gz: int_str.c
	python -m build

dist/int_str-1.0-cp310-cp310-linux_x86_64.whl: int_str.c
	python -m build

.PHONY: build
build: dist/int_str-1.0.tar.gz dist/int_str-1.0-cp310-cp310-linux_x86_64.whl
	python -m build

.PHONY: install
install: dist/int_str-1.0.tar.gz dist/int_str-1.0-cp310-cp310-linux_x86_64.whl
	pip install -e .

.PHONY: test
test: install
	pytest -v -s tests
