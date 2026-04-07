.PHONY: clean
clean:
	find . -type d | grep "/states$$" | xargs rm -r
