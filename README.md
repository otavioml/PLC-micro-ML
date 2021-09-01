# PLC-micro-ML
Final project for Programming languages class. It consists in a Lexer and a Parser build with SML to interpret and execute PLC language.

#How to execute
Follow the steps to create the .lex and the .yacc files. 

ml-lex PlcLexer.lex
ml-yacc PlcParser.yacc
sml testParser.sml

The last command run a sml file that contains a bunch of tests. It also enable SML programming through the command line.