CSE 535 Assignment 3
Name : Weituo Hao
ID : 109241801

Three algorithms are studied : Lamport Algorithm based on timestamp(LaTS), Ricart and Agrawala Algorithm based on 
timstamp(RATS), and Ricart and Agrawala Algorithm based on token(RAToken). All of them are written in TLA specification. 
I implemented LaTS algorithm according to the Lamport tutorial and part of the properties of RATS algorithm. Part of RATS and the whole RAToken algorithm are from the following source:
            RATS: https://www.loria.fr/~mery/aspd/ricartagrawala.tla 
            RAToken: https://sites.google.com/a/stonybrook.edu/sbcs535/projects-f13

To compare these algorithms, i ran them in toolbox as well as in command line. For command line i wrote the corresponding 
configuration file. 

1  Summarize and compare the specifications of the algorithms and correctness properties.
   In terms of size and ease of understanding, LaTS is easiest and has smaller size. Various aspects of LaTS and RATS follow 
   closely. Safety is specified in mutual exclusion and liveness propertiy is specified in starvation freedom or deadlock freedom 
   in these algorithms. And fairness is usually expressed with liveness. In summary, LaTS is more intuitive to understand but the    
   basis to further understand the other two.

2  Summarize and compare the ease and efficiency of running the checkers
   In toolbox, it is easier to initialize the model checker and adapt advanced options like key word redefinition. 
   In command line, we need to write another specification file and corresponding configuration file to initialize parameters. Some
   file directory issues may be met during the check.So the set up in command line is: 
   2.1 Put all supporting tla file and tla file under checking in the ../tla/tla2sany/StandardModules/ 
   2.2 After that, run the command java tlc2.TLC path-to-the-file/filename.tla 
   
   The following are the tables displaying above three algorithms under different processs numbers and the constraints

   LaTS:
   Procs    Nats    states   distinctstates    time
     2       5       36K        5K             0:03
     2       6       120K       18K            0:03
     3       2        6K        887            0:02
     3       3       397K       49K            0:04
     3       4      5670k       647K           0:26

   RATS:
   Procs    Nats    states   distinctstates    time
     2       5       560         59            0:01
     2       6       648         59            0:02
     3       2       282K        21K           0:07
     3       3       405K        20K           0:16
     3       4       521K        20K           0:23


   RAToken
   Procs    Nats    states    distinctstates  time
     2       2       27K         9472         0:03
     2       6        /           /            /
     3       2        /           /            /
     3       3        /           /            /
     3       4        /           /            /

The table indicates RATS's efficiency is relatvely higher than LaTS the takes less time under the same pair of parameters. There're
problems in the RAToken algorithm. For the first trial it took too much time for waiting i enforced to kill it. Then it did give results for smaller parameters but some TLC errors occurred. After that, every trial on this implementation will lead to crash of the toolbox.The error is caused from line 229 to line 231 by some value assertion. 
