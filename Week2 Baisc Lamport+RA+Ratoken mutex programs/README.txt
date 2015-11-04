CSE535 Asynchronous Systems  Assignment 2
Name : Weituo Hao
ID : 109241801

In this assignment correctness and performance are tested on the three algorithms:
1 Lamport's algorithm based on timestamps of a logical clock
2 Ricart and Agrawala's based on logical timestamps
3 Ricart and Agrawala's based on logical timestamps and token

The algorithm implementaions are from:
https://github.com/DistAlgo/distalgo

I changed a little bit of the original code like the task definition. And the rest of other parts are done by myself. 

For correctness:
Type in "python -m da main.da p r n" 
We will see sequential "in cs" and "out cs" in different colors in  console. The basic idea is: if two tasks 
conflict with each other, then we will see some "in cs" or "out cs" in a row rather than one after the other. 
At the end of the concole, we will see the summarized results including how many runs are successful and failed 
respectively in n runs. Also, we may see some intermediate files like output.txt, output1.txt...These files are 
the output for each algorithms.

For performance:
Type in "python -m da main.da p r s m"
We will see sequential "in cs" and "out cs" in different colors in console. I compared the running time of each algorithm 
under same parameter settings. For given number of processes, i draw the running time with respect to the requests. For 
given number of requests, i draw the running time with respect to the number of processes. We will see pictures stored in two
separate folders. From the curves, we will see the running time cost is Lamport's > RA logical time stamp > RA token. Note in 
some cases, it is not always true.  

Note that if type in "python -m da main.da p r", only Lamport's algorithm based on time stamp will be run. 
For some cases like large number of processes, we may come into a situation that the whole program hangs. This may be caused by the 
cmmunication protocol. For example, if in lamport's algorithm we use TCP protocol for the process communication and our computer 
has been connected to the Internet at the same time downloading files, uploading files, or openning many tabs in brower, then it is 
highly possible that the program will hang there for quite a long waiting time. We can change the communication way in da folder to 
improve the situation. But still, we can come across the same issue if the process and requests are too large.

