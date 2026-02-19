export {
  type InterviewState,
  type EntityDraft,
  type CommandDraft,
  QUESTION_TEMPLATES,
  InterviewStateMachine,
} from "./interview-state-machine"
export type { BlockingIssue } from "./blocking-policy"

import { InterviewStateMachine } from "./interview-state-machine"
import { exportInterviewStructuredSpec, renderInterviewSummary } from "./interview-adapters"

export class InterviewEngine extends InterviewStateMachine {
  getSummary (): string {
    return renderInterviewSummary(this.getState())
  }

  getStructuredSpec (): { spec: object; deployable: boolean; blocking_issues: Array<{ code: string; path: string; severity: string; message: string }> } {
    return exportInterviewStructuredSpec(this.getState())
  }
}
