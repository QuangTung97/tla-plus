.PHONY: clean
clean:
	find . -type d | grep "/states$$" | xargs rm -r

.PHONY: stat
stat:
	du -h -d0 .
