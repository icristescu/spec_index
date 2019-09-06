------------------------------- MODULE Simple -------------------------------
(***************************************************************************)
(* A simple specification of how the index works.                          *)
(* Three actions are specified: Find, Merge and Replace.                   *)
(***************************************************************************)
EXTENDS Naturals, Sequences
CONSTANT LogSize, MaxKey, MaxValue
NotFound == MaxValue + 2
Empty == MaxValue + 1

(* Types *) 
Key == 0..MaxKey
Value == 0..MaxValue
Entry == [{"key", "value"} -> Key \cup Value ] 

VARIABLES Log, Index, LogMem, entry
vars == << Log, Index, LogMem, entry >>

LogMemEmpty == [x \in Key |-> Empty]

TypeInvariant  == /\ entry \in [key : Key,  value : Value \cup {Empty}]
                  /\ LogMem \in [Key -> Value \cup {Empty}]
                  /\ Log \in Seq(Entry)
                  /\ Index \in Seq(Entry)

(***************************************************************************)
(* The initial state.                                                      *)
(***************************************************************************)         

Init == /\ Log = << >> 
        /\ Index = << >>
        /\ LogMem = LogMemEmpty
        /\ TypeInvariant

(***************************************************************************)
(* The actions.                                                            *)
(***************************************************************************)


(* Given a new entry, replace it in LogMem and append it to Log, while the 
   Log is not full. 
 *)

Replace(k,v) == /\ Len(Log) < LogSize
                /\ entry' = [key |-> k, value |-> v]
                /\ Log' = Append(Log, entry')
                /\ LogMem' = [LogMem EXCEPT ![k] = v]
                /\ UNCHANGED Index

(* Merge the Log and the Index once the Log is full. tmp is a temporary
   placeholder for Index.                        
   - If the Index is Empty then append the remaining LogMem to tmp            
   - Otherwise traverse the LogMem and compare entries from Index with
     the current key. The entry with the smallest key is appended to tmp.    
 *)

MakeEntry(k,v) == [key |-> k, value |-> v]

AppendRemainingLog(k,t,logmem) == 
    LET f[key\in Key, tmp\in Seq(Entry)] == 
         IF key >= MaxKey 
          THEN tmp     
          ELSE LET e == MakeEntry(k,logmem[k])
               IN f[key+1, Append(tmp,e)]
    IN f[k,t]    
    
MergeWith(i,logmem) ==  
    LET f[k\in Key, index\in Seq(Entry), tmp\in Seq(Entry)] == 
         IF k >= MaxKey 
          THEN tmp
          ELSE IF index = << >> 
                THEN AppendRemainingLog(k,tmp,logmem) 
                ELSE IF Head(index).key < k 
                 THEN f[k, Tail(index), Append(tmp, Head(index))]                       
                 ELSE LET e == MakeEntry(k,logmem[k])
                      IN f[k+1, index, Append(tmp, e)]
    IN f[0,i,<<>>]

Merge == /\ Len(Log) = LogSize
         /\ Index' = MergeWith(Index, LogMem)
         /\ Log' = <<>>
         /\ LogMem' = LogMemEmpty
         /\ UNCHANGED entry
         
(* Find an entry based on the key:                                          
   - Look first in LogMem                                                
   - If key not present in LogMem then look in Index                       
 *)
         
FindIndex(k,i) ==
    LET f[key\in Key, index\in Seq(Entry)] ==
         IF index = << >> 
          THEN NotFound 
          ELSE IF Head(index).key = key 
                THEN Head(index).value 
                ELSE f[key, Tail(index)]
    IN f[k,i]

Find(k) == /\ entry' = 
                LET vl == LogMem[k]   
                IN IF vl # Empty 
                    THEN MakeEntry(k, vl)
                    ELSE             
                     LET vi == FindIndex(k, Index) 
                     IN IF vi # Empty 
                         THEN MakeEntry(k, vi)
                         ELSE entry
           /\ UNCHANGED <<Log, LogMem, Index >> 
           
(***************************************************************************)
(* The Next state is obtained from the current state by doing a step of    *)
(* one of the available actions.                                           *)
(***************************************************************************)

Next == \/ (\E k \in Key : \E v \in Value : Replace(k,v)) 
        \/ Merge
        \/(\E k \in Key : Find(k)) 

(***************************************************************************)
(* Spec is the complete specification. The system begins in the state Init *)
(* and every step is either a Next step or leaves unchanged the variables  *)   
(* in vars.                                                                *)
(***************************************************************************)

Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* Properties the system should have. *)
(***************************************************************************)

LogSizeOK == [](Len(Log) =< LogSize)


(* Whenever the Log is full then eventually a merge occurs  *)
(*LogFullMerge == (Len(Log) = LogSize) ~> Merge*)
(* A merge leaves the log empty. *)
(*LogEmptyAfterMerge == []([Merge]_Log) => (Len(Log') = 0)*)
(*Once a merge occurs, then Index is never empty again. *)
(*IndexNotEmpty == [](Merge => [](Index # << >>))*)

-----------------------------------------------------------------------------
(* Model checking
   Unspecified Constants 
   (these values are small because the model checker is slow): 
     - LogSize = 2
     - MaxValue = 2
     - MaxKey = 9
   State Constraints:
     - Len(Index) < 8
   Invariants:
     - TypeOK
   Properties:
     - LogSizeOK
     - LogFullMerge
 *)

=============================================================================
\* Modification History
\* Last modified Fri Sep 06 11:08:27 CEST 2019 by icristes
\* Created Wed Sep 04 17:29:01 CEST 2019 by icristes
