all: compile example

default:
	if [ ! -d class ]; then mkdir class; fi;

compile: default
	javac sort/Main.java -d ./class

run: compile
	java -cp ./class sort.Main $(p1) $(p2) $(p3)

example:
	java -cp ./class sort.Main imagen1 30 bubble
