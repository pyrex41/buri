/-! Port of the part of `rocq/Observation.v` the Jit files use: the observation vocabulary,
outcomes and the generic reflexive-transitive closure `star`. Behaviors, refinement and the
determinism lemmas are not used by the Jit lowering files and are not ported (README). -/
namespace Observation

/-- Text is a sequence of Unicode scalar values. Rocq `N` is Lean `Nat`. -/
abbrev text := List Nat
abbrev byte := Nat

inductive direction | DIn | DOut deriving DecidableEq, Repr
inductive io_error
  | ENoEntity | EPermission | EBadHandle | ENoSpace | EClosed
  | EShortWrite | EProtocol | EOther (code : Nat)
  deriving DecidableEq, Repr

inductive request
  | QOpen (path : text) (d : direction)
  | QClose (h : Nat)
  | QRead (h : Nat) (max : Nat)
  | QWrite (h : Nat) (bytes : List byte)
  | QTime (clock : text)
  | QRandom (bound : Nat)
  deriving DecidableEq, Repr
inductive response
  | ROpened (h : Nat) | RClosed
  | RRead (bytes : List byte) | REof
  | RWrote (count : Nat)
  | RFailed (e : io_error)
  | RTime (t : Int) | RRandom (n : Nat)
  deriving DecidableEq, Repr

inductive signal | SigInt | SigTerm | SigKill | SigHup | SigOther (n : Nat) deriving DecidableEq, Repr
inductive env_event | Signal (s : signal) | Cancel deriving DecidableEq, Repr
inductive event | EvIO (q : request) (r : response) | EvEnv (e : env_event) deriving DecidableEq, Repr
inductive label | Tau | Obs (e : event) deriving DecidableEq, Repr
abbrev trace := List event
def trace_of : label → trace
  | .Tau => []
  | .Obs e => [e]

inductive resource | RHeap | RStack deriving DecidableEq, Repr

inductive outcome (V X : Type) where
  | Normal (v : V)
  | Error (x : X)
  | ResourceOut (r : resource)
  | Exit (code : Int)
  | Killed (s : signal)
  | Cancelled

section LTS
variable {S : Type} (step : S → label → S → Prop)

inductive star : S → trace → S → Prop
  | refl s : star s [] s
  | step s l s' t s'' : step s l s' → star s' t s'' → star s (trace_of l ++ t) s''

theorem star_trans {a b c : S} {t u : trace} (H : star step a t b) (K : star step b u c) :
    star step a (t ++ u) c := by
  induction H with
  | refl => exact K
  | step s l s' t s'' St _ ih => rw [List.append_assoc]; exact star.step _ _ _ _ _ St (ih K)
end LTS

end Observation
