import PfaffianDescent.CorayModelIncidenceOwnGenusWindow

namespace PfaffianDescent.Coray
set_option autoImplicit false

/-- The rank-one/proper-own-degree branch has the SAME strict scaled genus
window as the rank>=2 branch. Equality lambda=n is deliberately excluded. -/
theorem coray_modelField_scaledOwnGenus_lt_originalDegree_rankOne_proper001
    (r lambda n d : ℕ) (hR : r = 1) (hLambda : 1 ≤ lambda)
    (hProper : lambda < n) (hWindow : 1 + 3 * n.choose 2 ≤ d) :
    r * (1 + 3 * lambda.choose 2) < d := by
  subst r
  have hStep : 3 * (lambda + 1).choose 2 =
      3 * lambda.choose 2 + 3 * lambda := by
    simpa only [Nat.reduceAdd, Nat.choose_one_right, Nat.mul_add, Nat.add_comm] using
      congrArg (fun t : ℕ => 3 * t) (Nat.choose_succ_succ' lambda 1)
  have hChoose : (lambda + 1).choose 2 ≤ n.choose 2 :=
    Nat.choose_le_choose 2 (by omega)
  have hScale := Nat.mul_le_mul_left 3 hChoose
  have hStrict : 1 + 3 * lambda.choose 2 < 1 + 3 * n.choose 2 := by omega
  simpa only [Nat.one_mul] using hStrict.trans_le hWindow

end PfaffianDescent.Coray
