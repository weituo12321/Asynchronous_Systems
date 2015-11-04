CSE535 Asynchronous Systems  Assignment 2
Name: Weituo Hao 
ID: 109241801


In this assignment correctness and performance are tested on the four versions of Paxos:
1) Paxos
2) Paxos with preemption
3) Paxos with timeout
4) Paxos with preemption + timeout

Lamport's basis Paxos are from the following source:
http://drive.google.com/file/d/0B0MWH8ngLAIFN25GZzZzTWUIOVjA/view?usp=sharing

Based on the Paxos code above, i implemented the other three versions of Paxos and test the correctness 
in terms of safety and performance of elapsed time as well as cpu time.


1 Consider basic Paxos as described using itemized steps by Lamport in his "Paxos made simple" paper.
(1) What liveness problems does the algorithm have?
    The liveness may not be achieved because a single distinguished proposer may not be selected out since the proposer proposes
    a new proposal number at the same rate.

(2) What are possible methods for solving them?
    Some random factors like the network delay, preemption, and timeout technique to force the proposer proposes different proposal
    number.

2 Consider multi Paxos as described in pseudocode by van Renesse in his "Paxos made moderately complex" paper.
(1) What performance problems does the algorithm have?
    When acceptor returns a set of accepted proposal number and values, some items may be ignored.

(2) What are possible methods for solving them?
    For good performance, one would like the timeout period to be long enough so that a can be chosen successful but short enough so
    that ballots of a faulty leader are preempted quickly. The leader associates an initial timeout with each ballot. If a ballot gets
    preempted, the next ballot uses a timeout that is multiplied by some small factor larger than 1.



3 Meassure the correctness and performance of different versions of paxos

For correctness:
I implemented another process called Tester. Its function is to receive the learned values of learners.
The correctness means the tester should only receive repeated messages from learners. When the number 
of messages from learners are equal or greater than the number of learners, i chekced the set of mesages, it should 
be only one if it is correct. Otherwise, ouput tests failed. Note that i checked the correctness in each run. If you 
want to only see the correctness result you need to comment out the performance part. I suggest to run directly the performance
part since the correctness of each run will also be displayed in the terminal. Liveness is not guaranteed here. So the
program may get stuck there since no progress is made. Note that the liveness of the algorithm is not always achieved. 


For performance:
Type in "python -m da main.da p a l n r d w tp tl"  The results of pictures will be saved at the current_path/loss_results/, current_path/delay_results
and current_path/wait_results separately.
In particular, what i did was assigned parameters as p = a = l = 3, n= 10, r = 0.15, d = 5, w = 5, tp = 1, tl = 10

For parameter r, my program will run r/5, r*2/5, r*3/5, r*4/5 and r respectively, and compare the average elapsed time, cpu time,
the standard deviation of elapsed time, the standard deviation of cpu time of each version of Paxos.
Note that durint this round, the delay time is fixed as d/5 and wait time is fixed as w/5 second.
From the pictures, we may see that as the loss rate goes higher the average elapsed time and cpu time of original Paxos and Paxos 
with preemptions will keep at a relatively low level. Also, the elapsed standard deviation of origianl Paxos and Paxos with preemptions is 
less than the other two. However, the cpu time standard deviation of Paxos with timeout and preemption will lead the results as the 
loss rate becomes higher.An interesting result is the cpu time standard deviation of Paxos with preemption will drop fast as the loss 
rate gets higher.

For parameter d, my program will run ranges [0,d-4], [0, d-3], [0, d-2], [0, d-1], [0, d], and compare the same results as stated above. 
Note that during this round, the loss rate is fixed as r*3/5 and wait time as w/5 second.
From the pictures, we may see that as the delay time range increases, the average elapsed time and cpu time of all versions increase. Particularly, the increasing speed of Paxos with timeout preemtpiton is the smallest which means a more stable performance. Original 
Paxos performs worse since the average time goes fastest. An interesting result is the average elapsed time and cpu time of Paxos with 
timeout preemption seems to increase slower and slower. Since the increasing speed becomes slower, the standard deviation cpu time and 
elapsed time of Paxos with timeout preemption is the smallest since it is more stable. And the standard deviation elapsed time of original Paxos is the largest.In general, Paxos with timeout and preemption performs better under this experiment setting.

For parameter w, my program will run w/5, w*2/5, w*3/5, w*4/5 and w respectively, and compare the same reuslts as stated above.
Note that during this round, the loss rate is fixed as r*3/5 and the delay time is fixed as d/5 second.
From the pictures, we may see that as the wait time goes higher, the average cpu time of original Paxos performs better than the other 
three versions and the average elapsed time of Paxos with preemption performs better than the other three. In terms of the standard 
deviation of cpu time, all of the four versions become more and more stable where the origianl Paxos becomes stable faster than the
other three. But for the standard deviation of elapsed time, Paxos with preemption has a relatively smaller value than the other three.

Instructions:
1 For a better experiment, i suggest run each commented block separately in the code.
2 Note that all the observations are based on the result running on my own computer and parameter settings. As for other machines and other
parameters the conclusion stated above may vary! For a reference, i stored my results in the refer directory.
