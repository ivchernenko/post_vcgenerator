# poST verification condition generator
Generator of verification conditions for poST-programs in Isabelle/HOL format. This project based on poST language project (https://github.com/v-bashev/post_core).
# Implementation of the verification condition generator
- Implementatio of computing the strongest postcondition for simple statements [su.nsk.iae.post.parent/su.nsk.iae.post/src/su/nsk/iae/post/vcgenerator/Path.java](https://github.com/ivchernenko/post_vcgenerator/blob/main/su.nsk.iae.post.parent/su.nsk.iae.post/src/su/nsk/iae/post/vcgenerator/Path.java)
- Implementatio of computing the strongest postcondition for  top-level constructions (timeout statements, states, processes and programs) [su.nsk.iae.post.parent/su.nsk.iae.post/src/su/nsk/iae/post/vcgenerator/VCGenerator.java](https://github.com/ivchernenko/post_vcgenerator/blob/main/su.nsk.iae.post.parent/su.nsk.iae.post/src/su/nsk/iae/post/vcgenerator/VCGenerator.java)
- JAR file with the verification condition generator [vcgenerator.jar](https://github.com/ivchernenko/post_vcgenerator/blob/main/vcgenerator.jar)

# Examples
A collection of poST programs with a set of requirements, generated verification conditions and their proofs is contained in the directory [case-studies](https://github.com/ivchernenko/post_vcgenerator/tree/main/case-studies). This directory contains the corresponding subdirectories for each program:
- [HandDryer](https://github.com/ivchernenko/post_vcgenerator/tree/main/case-studies/HandDryer)--- hand dryer control program
- [escaalator](https://github.com/ivchernenko/post_vcgenerator/tree/main/case-studies/escalator)--- escalator control program
- [fridge](https://github.com/ivchernenko/post_vcgenerator/tree/main/case-studies/fridge)--- fridge control program
- [revolvingDoor](https://github.com/ivchernenko/post_vcgenerator/tree/main/case-studies/revolvingDoor)--- revolving door control program
- [thermopot](https://github.com/ivchernenko/post_vcgenerator/tree/main/case-studies/thermopot)--- thermopot control program
- [trafficLights](https://github.com/ivchernenko/post_vcgenerator/tree/main/case-studies/trafficLights)--- traffic lights control program
- [turnstile](https://github.com/ivchernenko/post_vcgenerator/tree/main/case-studies/turnstile)--- turnstile control program

Each directory has the following structure:
- File with the extension .post--- poST-программа
- File Requirements.txt--- requirements in natural language
- File Requirements.thy--- requirements in Isabelle/HOL
- Theory with the name that coincides with the program file name--- Isabelle/HOL theory with the verification conditions
- File VCTheoryLemmas.thy--- lemmas for the domain-specific functions with the proofs
- File ExtraInv.thy--- extra invariant
- Files Extra.thy--- proofs of the verification conditions for an extra invariant
- Files Proof.thy--- proofs of verification conditions for a requirement
# User manual
## Launching the program
To run the program on the user's computer, open the command line, go to the directory in which you want to create the theory file for Isabelle/HOL containing the verification conditions, and run the JAR file with the program. The program must be given the path to the source code file of the poST program as an argument. To do this, run the command `java -jar <vcgenerator.jar> <post_program>`. You can also specify the time interval corresponding to the activation period using the -i option. To do this, you need to run the command `java -jar <vcgenerator.jar> -i <interval> <post_program>` or `java -jar <vcgenerator.jar> <post_program> -i <interval>`, where <vcgenerator.jar> is the path to the JAR file of the program "Verification condition generator", <post_program> is the path to the file with the extension ".post", which contains the source code of the program in the poST language, and may also contain the configuration for this program, <interval> is the time interval corresponding to the activation period, specified in the same format as literals of the type TIME in the poST language.

If the poST program file contains a configuration for this program with an activation period specified, the value from the configuration is used as the activation period. The value of the -i option argument is not taken into account in this case. If the poST program file does not contain a configuration or does not specify an activation period value and the -i option is specified, the <interval> value is used as the activation period. Otherwise, the default value 100 ms is used as the activation period.
## Program execution
During execution, the program creates a file with the Isabelle/HOL theory with verification conditions in the current directory. The name of the created theory is obtained by encoding the name of the original file with the poST program without the extension using the characters allowed in the name of the Isabelle/HOL theory. Latin characters and numbers remain unchanged. Characters that cannot be contained in the theory name are replaced with __a_ where _a_ is the ASCII code of the character. If there are syntax errors in the poST program, the user is given error messages and correctness conditions are not generated.
