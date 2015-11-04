----------------MODULE rats  --------------------

(****************************************************************)
(* Mutual Exclusion Algorithm of Ricart and Agrawala            *)
(* It is based on the timestamples of Lamport and improves the  *)
(* initial distributed algoritrhm of Lamport by requiring at most*)
(* 2*(N-1) messages  for mutual exclusion request.               *)
(****************************************************************)


EXTENDS Naturals

CONSTANTS

	SITES, (* the set of sites in the network *)
        N,     (* the number of sites  *)
        NUM    (* the maximal value of timestample *)
VARIABLES
	osn,   (* Local number of each site        *)
        hsn,   (* Highest local number of other sites got till now *)
        orc,   (* Control of the numbers of REPLY messages received from others sites *)
	rd,    (* Control of deferred replies for sites *)
	working, (* Set of current sites working outside critical section *)
	updatingrc,  (* Control of the update of orc variables *)
	sendingrc, (* ASite in the set are sending requests to others ones *)
	requests, (* Model for request communication *)
	waiting,  (* Set of  sites waiting for N-1 replies *)
        replies, (* Model for replies communications *)
	cs,      (* Set of sites in the critical section *)
	defer,   (* When exiting the critical section, the site has to send the  deferred replies. *)
	message, (* Variable receiving the requests messages from request. *)
	rcs  (* Variable set to true when the site i requests the critical section *) 

----------------------------------------------------------

(****************************************************************)
(****************************************************************)
(* Phase Requesting Critical Section *)
(****************************************************************)
(****************************************************************)


(* Updating  the timestample of the current site *)
(* Requesting the critical section               *) 
 
Choose_a_sequence_number(site) ==
/\ site \in SITES 
/\ site \in working
/\ working' = working \ {site}
/\ updatingrc' = updatingrc \cup {site}
/\ osn' = [osn EXCEPT![site] = hsn[site] + 1]
/\ rcs' = [rcs EXCEPT![site] = 1]
/\ UNCHANGED <<hsn,orc,rd,sendingrc,requests,waiting,replies,cs,defer,message>>


(* Updating the number of sites which have to send an acknowledgement *)
(* The current site  will be waiting for authorizations of the other  *)
(* sites (N-1)                                                        *)

Updating_orc(site) ==
/\ site \in SITES 
/\ site \in updatingrc
/\ updatingrc' = updatingrc \ {site}
/\ sendingrc' = sendingrc \cup {site}
/\ orc' = [orc EXCEPT![site] = N-1]
/\ UNCHANGED <<osn,hsn,rd,working,requests,waiting,replies,cs,defer,message,rcs>>


(* Sending a request to every other site and asking them if  it can   *)
(* enter the critical section.                                        *)


Sending_request(site) ==
/\ site \in SITES 
/\ site \in sendingrc
/\ sendingrc' = sendingrc \ {site}
/\ waiting' = waiting \cup {site}
/\ requests' = requests \cup {request  \in [mes : {"request"},  sender : {site},  n : NUM, rec : SITES] : (request.sender = site) /\  (request.n=osn[site]) /\ (request.rec # site) }
/\ UNCHANGED <<osn,hsn,orc,rd,working,updatingrc,replies,cs,defer,message,rcs>>


(****************************************************************)
(****************************************************************)
(* Phase Waiting For  Critical Section *)
(****************************************************************)
(****************************************************************)



(* The site is waiting now for the N-1 replies for entering the critical section *)


Waiting_cs(site) ==
/\ site \in SITES 
/\ site \in waiting 
/\ orc[site]=0
/\ waiting' = waiting \ {site}
/\ cs' = cs \cup {site}
/\ UNCHANGED <<osn,hsn,orc,rd,working,updatingrc,sendingrc,requests,replies,defer,message,rcs>>



(****************************************************************)
(****************************************************************)
(* Phase Inside The   Critical Section *)
(****************************************************************)
(****************************************************************)

(****************************************************************)
(****************************************************************)
(* Phase Exit  The   Critical Section *)
(****************************************************************)
(****************************************************************)


(* The site decides to exit  the  critical section. It will be  in a control       *)
(* state where it has to process possible deferred messages  for requesting sites. *)
(* It is no more requesting the critical section.                                  *)

Out_cs(site) ==
/\ site \in SITES 
/\ site \in cs
/\ cs' = cs \ {site}
/\ defer' = defer \cup {site}
/\ rcs' = [rcs EXCEPT![site] = 0]
/\ UNCHANGED <<osn,hsn,orc,rd,working,updatingrc,sendingrc,requests,waiting,replies,message>>


(* When the site has sent every deferred site, it can go back to work. *)


Back_to_working(site) ==
/\ site \in SITES 
/\ { i  \in SITES : rd[site][i] = 0} = SITES
/\ site \in defer
/\ defer' = defer \ {site}
/\ working' = working \cup {site}
/\ UNCHANGED <<osn,hsn,orc,rd,updatingrc,sendingrc,requests,waiting,replies,cs,message,rcs>>


(* When a site is exiting the critical section, it  has to send to the waiting *)
(* sites a replies message. The replies message was deferred because the current   *)
(* site has a higher priority.  A new message is appe,nded to  the variable    *)
(* called replies          *)                                              


Replies_Deferred(site,osite) ==
/\ site \in SITES 
/\ osite \in SITES 
/\ site \in defer
/\ rd[site][osite] = 1
/\ rd' = [rd EXCEPT![site][osite] = 0]
/\ LET m == CHOOSE mm  \in  [mes : {"replye"},  sender : SITES, rec : SITES] :(
             /\ mm.sender = site
             /\ mm.rec = osite)
   IN
      /\ replies' = replies \cup {m}
/\ UNCHANGED <<osn,hsn,orc,working,updatingrc,sendingrc,requests,waiting,cs,defer,message,rcs>>






(****************************************************************)
(****************************************************************)
(* Processes managing messages got by the site                  *)
(****************************************************************)
(****************************************************************)


(* Receiving REPLIES messages *)


Getting_replies_messages(site,fromsite,m) ==
/\ site \in SITES 
/\ fromsite \in SITES 
/\ m \in replies 
/\ m.mes = "replye"
/\ m.sender = fromsite
/\ m.rec = site
/\ orc' = [orc EXCEPT![site] = @ - 1]
/\ replies' = replies \ {m}
/\ UNCHANGED <<osn,hsn,rd,working,updatingrc,sendingrc,requests,waiting,cs,defer,message,rcs>>






(* Receiving REQUEST messages *)
(* j sends a number to i *)
(* Updating the highest sequence number *)

UpdatingHSN(j,number,i,m) ==
/\ i \in SITES
/\ j \in SITES
/\ number \in NUM
/\ m \in requests 
/\ m.mes = "request"
/\ m.sender = j
/\ m.n = number
/\ m.rec = i
/\ LET max == IF hsn[i] < number THEN number ELSE hsn[i]
   IN hsn' = [hsn EXCEPT![i] = max]
/\ requests' = requests \ {m}
/\ message' = {m}
/\ UNCHANGED <<osn,orc,working,updatingrc,sendingrc,waiting,replies,cs,defer,rd,rcs>>


(* j sends a number to i *)
(* j has a priority higher than i *)


Defering_Reply(m) ==
/\ message={m}
/\  rcs[m.rec] = 1
/\ ((m.n > osn[ m.rec]) \/ (m.n=osn[ m.rec] /\ m.sender >  m.rec))
/\ rd' = [rd EXCEPT![ m.rec][ m.sender] = 1]
/\ message'={}
/\ UNCHANGED <<osn,hsn,orc,working,updatingrc,sendingrc,waiting,replies,cs,defer,requests,rcs>>



(* j sends a number to i            *)
(* j has a priority smaller  than i *)


ReplyACK(m) ==
/\ message={m}
/\ ~(/\ rcs[m.rec] = 1
     /\ ((m.n > osn[ m.rec]) \/ (m.n=osn[ m.rec] /\ m.sender >  m.rec)))
/\ message'={}
/\ LET r == CHOOSE mm \in  [mes : {"replye"},  sender : SITES, rec : SITES] :
              (
             /\ mm.sender = m.rec
             /\ mm.rec = m.sender)
   IN
      /\ replies' = replies \cup {r}
/\ UNCHANGED <<rd,osn,hsn,orc,working,updatingrc,sendingrc,waiting,cs,defer,requests,rcs>>



skip == UNCHANGED <<osn,hsn,orc,rd,working,updatingrc,sendingrc,requests,waiting,replies,cs,defer,message,rcs>>   

Next ==
\/  \E site \in SITES: Choose_a_sequence_number(site) 
\/  \E site \in SITES: Updating_orc(site)
\/  \E site \in SITES: Sending_request(site)
\/  \E site \in SITES: Waiting_cs(site)
\/  \E site \in SITES: Out_cs(site) 
\/  \E site \in SITES: Back_to_working(site)
\/  \E site \in SITES:  \E osite \in SITES:  Replies_Deferred(site,osite)
\/  \E site \in SITES:   \E fromsite \in SITES: \E m   \in  [mes : {"reply"},  sender : SITES, rec : SITES]: Getting_replies_messages(site,fromsite,m)
\/ \E i \in SITES:   \E j \in SITES:  \E number \in NUM: \E m \in [mes : {"request"},  sender : SITES,  n : NUM, rec : SITES]: UpdatingHSN(j,number,i,m) 
\/  \E i \in SITES:   \E j \in SITES:  \E number \in NUM: \E m \in [mes : {"request"},  sender : SITES,  n : NUM, rec : SITES]: Defering_Reply(m)
\/  \E i \in SITES:   \E j \in SITES:  \E number \in NUM: \E m \in [mes : {"request"},  sender : SITES,  n : NUM, rec : SITES]: ReplyACK(m)
\/ skip

Invariant ==   \A i \in SITES: \A j \in SITES : i \in cs /\ i # j => j \notin cs


Init == 
/\ osn=[ i \in SITES |->  0]
/\ rcs=[ i \in SITES |->  0]
/\ hsn=[ i \in SITES |->  0]
/\ orc = [ i \in SITES |->  0]
/\ rd = [ i \in SITES  |-> [j \in SITES  |-> 0]]
/\ requests = {}
/\ replies = {}
/\ working = SITES
/\ updatingrc = {}
/\ sendingrc = {}
/\ waiting = {}
/\ cs = {}
/\ defer = {}
/\ message = {}


(****************************************************************)
(* java tlc.TLC -modelcheck ricartagrawala *)
(****************************************************************)
(* Configuration file:                                          *)
(****************************************************************)
(*CONSTANTS
	N=3
	SITES = {1,2,3}
        NUM = {1,2,3}
   INIT Init              
   NEXT Next                

   INVARIANTS 
      Invariant
*)
(****************************************************************)
(****************************************************************)
(* Editing the file: *)
(****************************************************************)
(* java tlatex.TLA -shade -ptSize 12 ricartagrawala tla   *)
(****************************************************************)
(****************************************************************)


==================================================







