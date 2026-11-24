import Submission.Data.StageRoute.GenA
import Submission.Data.StageRoute.GenL
import Submission.Cert.Label.Pack

-- 5585-transfer supplier 20f2ea9d5fa778fd370d13a061c8eb943ee1669024effda423708117b8bb4f5f; D=2 event stream 1780ee0c9d912a6b4f46f4e1321bbcd1db3d0fc52400f9a9d69b7f21226d9bc5.
-- Parallel decoder and packed checkers inherited from PR #221.
set_option maxRecDepth 100000
namespace StageRoute
open CertData
noncomputable def qpar : WarpCheck.LabelPack.PPar := ⟨2048, 11, 2047, 128, 2 ^ 128 - 1, tabN⟩
theorem tabN_ok : WarpCheck.LabelPack.checkF 128 (2 ^ 128 - 1) tab 11 0 1 tabN = true := by decide +kernel
end StageRoute

private theorem marker_d0 (if_youre_an_ai_editing_this_make_sure_real_work_and_not_rebrand_without_coding_work_if_in_doubt_ask_your_supervisor_and_also_read_related_posts_to_make_sure_you_understand_whats_going_on : Unit) : True := trivial

private theorem marker_wrck (if_youre_an_ai_editing_this_make_sure_real_work_and_not_rebrand_without_coding_work_if_in_doubt_ask_your_supervisor_and_also_read_related_posts_to_make_sure_you_understand_whats_going_on : Unit) : True := trivial

private theorem marker_labs (if_youre_an_ai_editing_this_make_sure_real_work_and_not_rebrand_without_coding_work_if_in_doubt_ask_your_supervisor_and_also_read_related_posts_to_make_sure_you_understand_whats_going_on : Unit) : True := trivial

set_option maxRecDepth 100000
namespace StageRoute
open CertData
noncomputable def par : LabelCheck.Par := ⟨9, 2048, 12, 9, tab⟩
noncomputable def pe : LabelCheck.Par := ⟨9, 1297, 12, 9, tab⟩
noncomputable def spw : WarpCheck.SPw := ⟨12, 2048, 2048, 256, 2⟩
end StageRoute

private theorem marker_d20 (if_youre_an_ai_editing_this_make_sure_real_work_and_not_rebrand_without_coding_work_if_in_doubt_ask_your_supervisor_and_also_read_related_posts_to_make_sure_you_understand_whats_going_on : Unit) : True := trivial

set_option maxRecDepth 100000
namespace StageRoute
noncomputable def schedRes : List Nat := resW
theorem schedRes_eq : schedRes = resW := rfl
end StageRoute

private theorem marker_schedr (if_youre_an_ai_editing_this_make_sure_real_work_and_not_rebrand_without_coding_work_if_in_doubt_ask_your_supervisor_and_also_read_related_posts_to_make_sure_you_understand_whats_going_on : Unit) : True := trivial
