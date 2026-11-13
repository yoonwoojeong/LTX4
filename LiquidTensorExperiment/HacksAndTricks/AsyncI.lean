
#align_import hacks_and_tricks.asyncI

namespace Tactic

unsafe def prove_goal_asyncI (tac : tactic Unit) : tactic Unit := do
  let ctx ← local_context
  unfreezing (revert_lst ctx)
  let tgt ← target
  let tgt ← instantiate_mvars tgt
  let env ← get_env
  let tgt ← return <| env.unfold_untrusted_macros tgt
  when tgt (fail "goal contains metavariables")
  let params ← return tgt.collect_univ_params
  let lemma_name ← new_aux_decl_name
  let proof ←
    run_async do
        let goal_meta ← mk_meta_var tgt
        set_goals [goal_meta]
        ctx fun c => unfreezing (intro c)
        tac
        let proof ← instantiate_mvars goal_meta
        let proof ← return <| env.unfold_untrusted_macros proof
        when proof <| fail "async proof failed: contains metavariables"
        return proof
  add_decl <| declaration.thm lemma_name params tgt proof
  exact (expr.const lemma_name (params level.param))

namespace Interactive

open Interactive.Types

/-- Proves the first goal asynchronously as a separate lemma. -/
unsafe def asyncI (tac : itactic) : tactic Unit :=
  prove_goal_asyncI tac

end Interactive

end Tactic

