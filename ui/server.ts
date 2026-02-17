import { readFile } from "node:fs/promises"
import { join, extname } from "node:path"

const MIME_TYPES: Record<string, string> = {
  ".html": "text/html",
  ".js": "application/javascript",
  ".css": "text/css",
  ".json": "application/json",
  ".png": "image/png",
  ".svg": "image/svg+xml",
  ".woff": "font/woff",
  ".woff2": "font/woff2",
}

export interface UiServerConfig {
  uiPath: string
  apiUrl: string
}

export class UiServer {
  private uiPath: string
  private apiUrl: string

  constructor(config: UiServerConfig) {
    this.uiPath = config.uiPath
    this.apiUrl = config.apiUrl
  }

  async handleRequest(req: Request): Promise<Response> {
    const url = new URL(req.url)
    const pathname = url.pathname

    if (pathname.startsWith("/api/")) {
      return this.handleApiRequest(req, pathname)
    }

    if (pathname.startsWith("/ui/")) {
      return this.handleUiFile(pathname.slice(4))
    }

    if (pathname === "/" || pathname === "/index.html") {
      return this.handleIndexHtml()
    }

    return new Response("Not Found", { status: 404 })
  }

  private async handleApiRequest(req: Request, pathname: string): Promise<Response> {
    const apiTarget = `${this.apiUrl}/api/${pathname.slice(5)}`

    const response = await fetch(apiTarget, {
      method: req.method,
      headers: {
        ...Object.fromEntries(req.headers.entries()),
        "x-ui-request": "true",
      },
      body: req.method !== "GET" && req.method !== "HEAD" ? await req.text() : undefined,
    })

    return new Response(response.body, {
      status: response.status,
      headers: {
        ...Object.fromEntries(response.headers.entries()),
        "Access-Control-Allow-Origin": "*",
      },
    })
  }

  private async handleUiFile(filename: string): Promise<Response> {
    try {
      const filePath = join(this.uiPath, filename)
      const content = await readFile(filePath)
      const ext = extname(filename)
      const contentType = MIME_TYPES[ext] || "application/octet-stream"

      return new Response(content, {
        headers: {
          "Content-Type": contentType,
          "Cache-Control": "public, max-age=31536000",
        },
      })
    } catch {
      return new Response("Not Found", { status: 404 })
    }
  }

  private async handleIndexHtml(): Promise<Response> {
    try {
      const indexPath = join(this.uiPath, "index.html")
      const content = await readFile(indexPath, "utf-8")

      const html = content
        .replace(/\{\{API_URL\}\}/g, this.apiUrl)
        .replace(/\{\{UI_BASE\}\}/g, "/ui")

      return new Response(html, {
        headers: { "Content-Type": "text/html" },
      })
    } catch {
      return new Response(this.getDefaultIndexHtml(), {
        headers: { "Content-Type": "text/html" },
      })
    }
  }

  private getDefaultIndexHtml(): string {
    return `<!DOCTYPE html>
<html>
<head>
  <meta charset="utf-8">
  <meta name="viewport" content="width=device-width, initial-scale=1">
  <title>CICSC App</title>
  <script src="{{UI_BASE}}/app.js" type="module"></script>
  <style>
    * { box-sizing: border-box; margin: 0; padding: 0; }
    body { font-family: -apple-system, BlinkMacSystemFont, 'Segoe UI', Roboto, sans-serif; }
  </style>
</head>
<body>
  <div id="app"></div>
</body>
</html>`
  }
}
