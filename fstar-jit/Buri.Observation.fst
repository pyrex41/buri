(* Port of rocq/Observation.v, the slice the Jit files use: text, IO events, labels, traces,
   outcomes, and `star`. The coinductive behaviors (stream, silent_forever, reacts_forever,
   behaves) and the refinement theorems over them are not ported: no Jit file uses them. *)
module Buri.Observation
open Buri.Lib

type text = list nat
type byte = nat
let byte_ok (b : byte) : bool = b < 256

type direction = | DIn | DOut
type io_error =
  | ENoEntity | EPermission | EBadHandle | ENoSpace | EClosed
  | EShortWrite
  | EProtocol
  | EOther of nat

type request =
  | QOpen : path:text -> d:direction -> request
  | QClose : h:nat -> request
  | QRead : h:nat -> max:nat -> request
  | QWrite : h:nat -> bytes:list byte -> request
  | QTime : clock:text -> request
  | QRandom : bound:nat -> request
type response =
  | ROpened : h:nat -> response
  | RClosed
  | RRead : bytes:list byte -> response
  | REof
  | RWrote : count:nat -> response
  | RFailed : e:io_error -> response
  | RTime : t:int -> response
  | RRandom : n:nat -> response

type signal = | SigInt | SigTerm | SigKill | SigHup | SigOther of nat
type env_event = | Signal of signal | Cancel

type event = | EvIO : q:request -> r:response -> event | EvEnv : e:env_event -> event
type label = | Tau | Obs of event
type trace = list event
let trace_of (l : label) : trace = match l with Tau -> [] | Obs e -> [e]

type resource = | RHeap | RStack
type outcome (v x : Type) =
  | Normal : v -> outcome v x
  | Error : x -> outcome v x
  | ResourceOut : resource -> outcome v x
  | Exit : int -> outcome v x
  | Killed : signal -> outcome v x
  | Cancelled : outcome v x

(* star over a labeled step relation, as an inductive family (Rocq: Inductive ... : Prop). *)
noeq type star (#s : Type) (step : s -> label -> s -> Type) : s -> trace -> s -> Type =
  | Star_refl : x:s -> star step x [] x
  | Star_step : x:s -> l:label -> x1:s -> t:trace -> x2:s ->
      step x l x1 -> star step x1 t x2 -> star step x (app (trace_of l) t) x2

let rec star_trans (#s : Type) (#step : s -> label -> s -> Type) (#a #b #c : s) (#t #u : trace)
  (h : star step a t b) (k : star step b u c) : Tot (star step a (app t u) c) (decreases h) =
  match h with
  | Star_refl _ -> k
  | Star_step x l x1 t1 _ st rest ->
    app_assoc (trace_of l) t1 u;
    Star_step x l x1 (app t1 u) c st (star_trans rest k)
