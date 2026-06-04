.PHONY: clean
clean:
	find . -type d | grep "/states$$" | xargs --no-run-if-empty rm -r
	find . -type f | grep "_trace_T" | xargs --no-run-if-empty rm

.PHONY: stat
stat:
	du -h -d0 .
