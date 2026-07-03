import Init

/-!
# Master slice partition bridge

This module is a partition bridge only. It defines the master obligated-row
index as the disjoint sum of the 53 completed slice row-count families and
proves structural partition facts. The row-to-slice-theorem-file mapping is
certified by the companion CSV/JSON artifacts. This module deliberately does
not state or prove the row coverage predicate, any local-layer theorem, any
finite-prefix theorem, or any global shifted-prime theorem.
-/

namespace Erdos647ShiftedPrimeChannel

inductive TailKillMasterSliceId where
  | s0_9
  | s10_19
  | s20_29
  | s30_39
  | s40_49
  | s50_59
  | s60_69
  | s70_79
  | s80_89
  | s90_99
  | s100_109
  | s110_119
  | s120_129
  | s130_139
  | s140_149
  | s150_159
  | s160_169
  | s170_179
  | s180_189
  | s190_199
  | s200_209
  | s210_219
  | s220_229
  | s230_239
  | s240_249
  | s250_259
  | s260_269
  | s270_279
  | s280_289
  | s290_299
  | s300_309
  | s310_319
  | s320_329
  | s330_339
  | s340_349
  | s350_359
  | s360_369
  | s370_379
  | s380_389
  | s390_399
  | s400_409
  | s410_419
  | s420_429
  | s430_439
  | s440_449
  | s450_459
  | s460_469
  | s470_479
  | s480_489
  | s490_499
  | s500_509
  | s510_519
  | s520_528
deriving DecidableEq, Repr

def tailKillMasterSliceIds : List TailKillMasterSliceId :=
  [TailKillMasterSliceId.s0_9, TailKillMasterSliceId.s10_19, TailKillMasterSliceId.s20_29, TailKillMasterSliceId.s30_39, TailKillMasterSliceId.s40_49, TailKillMasterSliceId.s50_59, TailKillMasterSliceId.s60_69, TailKillMasterSliceId.s70_79, TailKillMasterSliceId.s80_89, TailKillMasterSliceId.s90_99, TailKillMasterSliceId.s100_109, TailKillMasterSliceId.s110_119, TailKillMasterSliceId.s120_129, TailKillMasterSliceId.s130_139, TailKillMasterSliceId.s140_149, TailKillMasterSliceId.s150_159, TailKillMasterSliceId.s160_169, TailKillMasterSliceId.s170_179, TailKillMasterSliceId.s180_189, TailKillMasterSliceId.s190_199, TailKillMasterSliceId.s200_209, TailKillMasterSliceId.s210_219, TailKillMasterSliceId.s220_229, TailKillMasterSliceId.s230_239, TailKillMasterSliceId.s240_249, TailKillMasterSliceId.s250_259, TailKillMasterSliceId.s260_269, TailKillMasterSliceId.s270_279, TailKillMasterSliceId.s280_289, TailKillMasterSliceId.s290_299, TailKillMasterSliceId.s300_309, TailKillMasterSliceId.s310_319, TailKillMasterSliceId.s320_329, TailKillMasterSliceId.s330_339, TailKillMasterSliceId.s340_349, TailKillMasterSliceId.s350_359, TailKillMasterSliceId.s360_369, TailKillMasterSliceId.s370_379, TailKillMasterSliceId.s380_389, TailKillMasterSliceId.s390_399, TailKillMasterSliceId.s400_409, TailKillMasterSliceId.s410_419, TailKillMasterSliceId.s420_429, TailKillMasterSliceId.s430_439, TailKillMasterSliceId.s440_449, TailKillMasterSliceId.s450_459, TailKillMasterSliceId.s460_469, TailKillMasterSliceId.s470_479, TailKillMasterSliceId.s480_489, TailKillMasterSliceId.s490_499, TailKillMasterSliceId.s500_509, TailKillMasterSliceId.s510_519, TailKillMasterSliceId.s520_528]

def tailKillMasterSliceRowCount : TailKillMasterSliceId -> Nat
  | TailKillMasterSliceId.s0_9 => 17084
  | TailKillMasterSliceId.s10_19 => 17138
  | TailKillMasterSliceId.s20_29 => 17052
  | TailKillMasterSliceId.s30_39 => 17236
  | TailKillMasterSliceId.s40_49 => 17060
  | TailKillMasterSliceId.s50_59 => 16824
  | TailKillMasterSliceId.s60_69 => 17112
  | TailKillMasterSliceId.s70_79 => 17396
  | TailKillMasterSliceId.s80_89 => 17166
  | TailKillMasterSliceId.s90_99 => 16942
  | TailKillMasterSliceId.s100_109 => 17440
  | TailKillMasterSliceId.s110_119 => 17020
  | TailKillMasterSliceId.s120_129 => 17068
  | TailKillMasterSliceId.s130_139 => 16940
  | TailKillMasterSliceId.s140_149 => 17170
  | TailKillMasterSliceId.s150_159 => 16944
  | TailKillMasterSliceId.s160_169 => 17084
  | TailKillMasterSliceId.s170_179 => 17120
  | TailKillMasterSliceId.s180_189 => 17048
  | TailKillMasterSliceId.s190_199 => 17006
  | TailKillMasterSliceId.s200_209 => 16552
  | TailKillMasterSliceId.s210_219 => 17114
  | TailKillMasterSliceId.s220_229 => 16706
  | TailKillMasterSliceId.s230_239 => 17136
  | TailKillMasterSliceId.s240_249 => 17280
  | TailKillMasterSliceId.s250_259 => 16654
  | TailKillMasterSliceId.s260_269 => 17290
  | TailKillMasterSliceId.s270_279 => 17336
  | TailKillMasterSliceId.s280_289 => 16978
  | TailKillMasterSliceId.s290_299 => 16828
  | TailKillMasterSliceId.s300_309 => 16950
  | TailKillMasterSliceId.s310_319 => 16938
  | TailKillMasterSliceId.s320_329 => 16934
  | TailKillMasterSliceId.s330_339 => 17288
  | TailKillMasterSliceId.s340_349 => 16904
  | TailKillMasterSliceId.s350_359 => 17040
  | TailKillMasterSliceId.s360_369 => 16816
  | TailKillMasterSliceId.s370_379 => 16932
  | TailKillMasterSliceId.s380_389 => 16948
  | TailKillMasterSliceId.s390_399 => 16890
  | TailKillMasterSliceId.s400_409 => 17308
  | TailKillMasterSliceId.s410_419 => 17042
  | TailKillMasterSliceId.s420_429 => 17130
  | TailKillMasterSliceId.s430_439 => 17094
  | TailKillMasterSliceId.s440_449 => 17062
  | TailKillMasterSliceId.s450_459 => 17148
  | TailKillMasterSliceId.s460_469 => 16798
  | TailKillMasterSliceId.s470_479 => 16882
  | TailKillMasterSliceId.s480_489 => 16888
  | TailKillMasterSliceId.s490_499 => 17308
  | TailKillMasterSliceId.s500_509 => 17024
  | TailKillMasterSliceId.s510_519 => 17212
  | TailKillMasterSliceId.s520_528 => 15436

theorem tailKillMasterSliceIds_length :
    tailKillMasterSliceIds.length = 53 := by
  native_decide

theorem tailKillMasterSliceRowCount_sum :
    (tailKillMasterSliceIds.map tailKillMasterSliceRowCount).sum = 901696 := by
  native_decide

def TailKillMasterRowsOfSlice : TailKillMasterSliceId -> Type
  | sliceId => Fin (tailKillMasterSliceRowCount sliceId)

abbrev TailKillMasterRowIndex : Type :=
  Sigma TailKillMasterRowsOfSlice

def tailKillMasterSliceOf :
    TailKillMasterRowIndex -> TailKillMasterSliceId
  | ⟨sliceId, _⟩ => sliceId

def tailKillMasterSliceContains
    (sliceId : TailKillMasterSliceId)
    (idx : TailKillMasterRowIndex) : Prop :=
  tailKillMasterSliceOf idx = sliceId

theorem tailKillMasterSliceMembership_unique
    (idx : TailKillMasterRowIndex)
    {sliceId : TailKillMasterSliceId}
    (h : tailKillMasterSliceContains sliceId idx) :
    sliceId = tailKillMasterSliceOf idx := by
  exact h.symm

theorem tailKillMasterSliceMembership_eq
    {sliceA sliceB : TailKillMasterSliceId}
    {idx : TailKillMasterRowIndex}
    (hA : tailKillMasterSliceContains sliceA idx)
    (hB : tailKillMasterSliceContains sliceB idx) :
    sliceA = sliceB := by
  exact hA.symm.trans hB

def tailKillMasterRowIndexToSigma :
    TailKillMasterRowIndex -> Sigma TailKillMasterRowsOfSlice :=
  id

def tailKillMasterRowIndexOfSigma :
    Sigma TailKillMasterRowsOfSlice -> TailKillMasterRowIndex :=
  id

theorem tailKillMasterRowIndex_sigma_left_inverse :
    Function.LeftInverse
      tailKillMasterRowIndexOfSigma
      tailKillMasterRowIndexToSigma := by
  intro idx
  rfl

theorem tailKillMasterRowIndex_sigma_right_inverse :
    Function.RightInverse
      tailKillMasterRowIndexOfSigma
      tailKillMasterRowIndexToSigma := by
  intro idx
  rfl

end Erdos647ShiftedPrimeChannel
