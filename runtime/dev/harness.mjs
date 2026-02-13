#!/usr/bin/env node
import { createServer } from "node:http"
import worker from "../http/worker.ts"
import { makeSqliteFileD1 } from "./sqlite-d1-file.mjs"

const port = Number(process.env.PORT ?? 8787)
const dbPath = process.env.CICSC_DB_PATH ?? "./cicsc.dev.sqlite"

const env = {
  DB: makeSqliteFileD1(dbPath),
  BUNDLE_CREATE_TOKEN: process.env.CICSC_BUNDLE_CREATE_TOKEN,
  TENANT_BIND_TOKEN: process.env.CICSC_TENANT_BIND_TOKEN,
  TENANT_MIGRATE_TOKEN: process.env.CICSC_TENANT_MIGRATE_TOKEN,
}

const server = createServer(async (req, res) => {
  try {
    const body = await readBody(req)
    const url = `http://localhost:${port}${req.url ?? "/"}`
    const request = new Request(url, {
      method: req.method ?? "GET",
      headers: req.headers,
      body: body.length > 0 ? body : undefined,
    })

    const response = await worker.fetch(request, env)
    res.statusCode = response.status
    response.headers.forEach((v, k) => res.setHeader(k, v))
    const buf = Buffer.from(await response.arrayBuffer())
    res.end(buf)
  } catch (e) {
    res.statusCode = 500
    res.setHeader("content-type", "application/json")
    res.end(JSON.stringify({ ok: false, error: e?.message ?? String(e) }))
  }
})

server.listen(port, () => {
  process.stdout.write(`cicsc dev harness listening on http://localhost:${port}\n`)
  process.stdout.write(`sqlite file: ${dbPath}\n`)
})

function readBody (req) {
  return new Promise((resolve, reject) => {
    const parts = []
    req.on("data", (d) => parts.push(d))
    req.on("end", () => resolve(Buffer.concat(parts)))
    req.on("error", reject)
  })
}
