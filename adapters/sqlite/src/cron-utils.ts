import parser from "cron-parser"

/**
 * Compute the next run time from a cron expression.
 * @param expression Cron expression (e.g. "0 9 * * MON-FRI")
 * @param after Unix ms after which to find the next run (default: now)
 * @param timezone Timezone (e.g. "America/New_York")
 * @returns Unix ms of the next run
 */
export function getNextCronRun (expression: string, after: number = Date.now(), timezone?: string): number {
  const options = {
    currentDate: new Date(after),
    tz: timezone,
  }
  const interval = parser.parseExpression(expression, options)
  return interval.next().getTime()
}
