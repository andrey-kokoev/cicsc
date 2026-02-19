import { spawnSync } from "node:child_process"

spawnSync("./control-plane/scripts/missing_helper.sh", {
  cwd: process.cwd(),
  encoding: "utf8",
})
