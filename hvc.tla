-------------------- MODULE hvc -------------------
\* AUTHORS
\* Charuvahan Adhivarahan (charuvah@buffalo.edu) (UB Person#: 50168105)
\* Lalith Vikram Natarajan (lalithvi@buffalo.edu) (UB Person#: 50169243)

EXTENDS Integers, TLC
CONSTANT N, STOP, EPS
ASSUME N \in Nat
Procs == 1..N

SetMax(S) == CHOOSE i \in S : \A j \in S : i >= j
Max(X, Y) == IF X > Y THEN X ELSE Y

(* Hybrid Vector Clocks algorithm
--algorithm hvc {
  variable pt = [j \in Procs |-> 0]; msg = [j \in Procs |-> [k \in Procs |-> 0]];
  
  fair process (j \in Procs)
  variable v = [k \in Procs |-> 0];
  {J0:while (pt[self] < STOP) { 
            either 
            Recv:{ \* local or receive event
                    await(\A k \in Procs: pt[self] < pt[k]+ EPS); \* NTP clock sync
                    pt[self] := pt[self]+1;
                    v := [k \in Procs |-> IF k = self THEN pt[self] ELSE Max(v[k], msg[self][k])];
                } 
            or
            Send:{ \* send event
                    await(\A k \in Procs: pt[self] < pt[k]+ EPS); \* NTP clock sync
                    pt[self] := pt[self]+1;
                    v[self] := pt[self];
                    with (k \in Procs \ {self}) {
                        msg[k] := v;
                    }
                }        
        } 
  }
}
*)
\* BEGIN TRANSLATION
VARIABLES pt, msg, pc, v

vars == << pt, msg, pc, v >>

ProcSet == (Procs)

Init == (* Global variables *)
        /\ pt = [j \in Procs |-> 0]
        /\ msg = [j \in Procs |-> [k \in Procs |-> 0]]
        (* Process j *)
        /\ v = [self \in Procs |-> [k \in Procs |-> 0]]
        /\ pc = [self \in ProcSet |-> "J0"]

J0(self) == /\ pc[self] = "J0"
            /\ IF pt[self] < STOP
                  THEN /\ \/ /\ pc' = [pc EXCEPT ![self] = "Recv"]
                          \/ /\ pc' = [pc EXCEPT ![self] = "Send"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
            /\ UNCHANGED << pt, msg, v >>

Recv(self) == /\ pc[self] = "Recv"
              /\ (\A k \in Procs: pt[self] < pt[k]+ EPS)
              /\ pt' = [pt EXCEPT ![self] = pt[self]+1]
              /\ v' = [v EXCEPT ![self] = [k \in Procs |-> IF k = self THEN pt'[self] ELSE Max(v[self][k], msg[self][k])]]
              /\ pc' = [pc EXCEPT ![self] = "J0"]
              /\ msg' = msg

Send(self) == /\ pc[self] = "Send"
              /\ (\A k \in Procs: pt[self] < pt[k]+ EPS)
              /\ pt' = [pt EXCEPT ![self] = pt[self]+1]
              /\ v' = [v EXCEPT ![self][self] = pt'[self]]
              /\ \E k \in Procs \ {self}:
                   msg' = [msg EXCEPT ![k] = v'[self]]
              /\ pc' = [pc EXCEPT ![self] = "J0"]

j(self) == J0(self) \/ Recv(self) \/ Send(self)

Next == (\E self \in Procs: j(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Procs : WF_vars(j(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

\* Boundedness
TypeOK == (\A k \in Procs: v[k][k] = pt[k])
Sync == (\A k,m \in Procs: pt[k] <= pt[m]+EPS)
Safety1 == (\A k \in Procs: v[k][k] >= pt[k] /\ v[k][k] <= pt[k]+EPS)
Safety2 == (\A k,l \in Procs: v[k][k] >= v[l][k])
\* Stabilization

==================================================
