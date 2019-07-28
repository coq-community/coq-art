Inductive vehicle : Set :=
  | bicycle (seats: nat)
  | motorized (seats wheels: nat).


Definition nb_seats  : vehicle -> nat :=
 vehicle_rec (fun v => nat) 
              (fun nseats => nseats)
              (fun nbseats nbwheels => nbseats).
Definition nb_seats' (v : vehicle) :  nat :=
 match v with
   | bicycle  i => i
   | motorized i _ => i
 end.

(** Tests: 
Compute nb_seats (bicycle 1).


Compute nb_seats (motorized 50 4).

*)
