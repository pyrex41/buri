(* Translation validation of this exact source/KLambda/Scheme artifact chain.
   Universal in runtime data, not a theorem about all compiler inputs. The
   truthfulness of native reading, capture, installation and IO is separate. *)
From Coq Require Import List String.
From Buri Require Import Wire Encoder EncoderSource EncoderNames EncoderScheme
 EncoderFrontend ObservedEncoder ObservedCapture Sealed SealedInput SourceReader
 Native NativeRuntime NativeCodec AdapterCorrect.
Import ListNotations.
Module CodecCorrespondence.
Module C := NativeCodec.NativeCodec.
Module O := ObservedEncoder.ObservedEncoder.
Module F := EncoderFrontend.EncoderFrontend.
Module N := Native.Native.
(* The two literal artifacts must contain the very same paired compiler
   records, not merely pass independent validators. *)
Definition sealed_records := match SealedCapture.unpack sealed_text with
 | Some root => match F.elements root with Some [_;records;_] => Some records | _ => None end
 | _ => None end.
Definition observed_records := match O.check_capture 250 observed_encoder_text with
 | Some (_,root,_,_) => Some root | _ => None end.
Local Transparent sealed_text observed_encoder_text.
Theorem exact_compiler_records : sealed_records = observed_records.
Proof. vm_compute. reflexivity. Qed.
Theorem compiler_records_present : exists records,
 sealed_records = Some records /\ observed_records = Some records.
Proof. vm_compute. eexists; split; reflexivity. Qed.
Local Opaque sealed_text observed_encoder_text.
Theorem source_to_machine :
 SourceReader.read encoder_source_text = Some SourceReader.forms /\
 encoder_source_text = Encoder.source /\
 sealed_records = observed_records /\
 forall d, exists steps,
 NativeRuntime.invoke steps sealed_native_program "kl:buri.wire" [C.native d] =
 N.Returned (N.Text (Wire.capture (C.wire d))).
Proof.
 split; [apply SourceReader.encoder_source_parsed|].
 split; [apply encoder_source_exact|].
 split; [apply exact_compiler_records|apply C.machine_correct].
Qed.
Theorem compiled_output_agrees : forall raw root sp tp,
 O.check_capture 250 observed_encoder_text = Some (raw,root,sp,tp) ->
 forall d fuel v,
 EncoderNames.eval fuel sp
   (EncoderNames.arguments (EncoderNames.parameters (sp Encoder.Datum))
      (Encoder.Data (C.wire d)) (Encoder.Number 0))
   (EncoderNames.expression (sp Encoder.Datum)) = Encoder.Returned v ->
 exists steps,
 v = Encoder.Text (Wire.capture (C.wire d)) /\
 NativeRuntime.invoke steps sealed_native_program "kl:buri.wire" [C.native d] =
 N.Returned (N.Text (Wire.capture (C.wire d))).
Proof.
 intros raw root sp tp H d fuel v E.
 destruct (O.accepted_sound 250 observed_encoder_text observed_encoder_checked)
 as [raw' [root' [sp' [tp' [CHECK [_ [_ [S T]]]]]]]].
 rewrite H in CHECK; inversion CHECK; subst.
 assert (V : v = Encoder.Text (Wire.capture (C.wire d))) by
   (eapply EncoderNames.program_encoder_unique; eauto).
 destruct (C.machine_correct d) as [steps M]. exists steps; split; assumption.
Qed.
Theorem source_machine_total :
 SourceReader.read encoder_source_text = Some SourceReader.forms /\
 exists raw root sp tp,
 O.check_capture 250 observed_encoder_text = Some (raw,root,sp,tp) /\
 (forall d, exists fuel steps,
 EncoderNames.eval fuel sp
   (EncoderNames.arguments (EncoderNames.parameters (sp Encoder.Datum))
      (Encoder.Data (C.wire d)) (Encoder.Number 0))
   (EncoderNames.expression (sp Encoder.Datum)) =
 Encoder.Returned (Encoder.Text (Wire.capture (C.wire d))) /\
 NativeRuntime.invoke steps sealed_native_program "kl:buri.wire" [C.native d] =
 N.Returned (N.Text (Wire.capture (C.wire d)))).
Proof.
 split; [apply SourceReader.encoder_source_parsed|].
 destruct (O.accepted_sound 250 observed_encoder_text observed_encoder_checked)
 as [raw [root [sp [tp [CHECK [_ [_ [S T]]]]]]]].
 exists raw,root,sp,tp; split; [exact CHECK|]. intro d.
 destruct (EncoderNames.program_encoder_total sp S (C.wire d)) as [fuel E].
 destruct (C.machine_correct d) as [steps M]. exists fuel,steps; split; assumption.
Qed.
End CodecCorrespondence.
