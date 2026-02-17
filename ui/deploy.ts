export interface DeploymentResult {
  ok: boolean
  url?: string
  error?: string
}

export interface UIDeploymentAdapter {
  name: string
  deploy(config: {
    uiPath: string
    apiUrl: string
    projectName?: string
  }): Promise<DeploymentResult>
}

export function createDeploymentAdapter(type: string): UIDeploymentAdapter {
  switch (type) {
    case "cloudflare-pages":
      return new CloudflarePagesAdapter()
    case "vercel":
      return new VercelAdapter()
    case "netlify":
      return new NetlifyAdapter()
    default:
      throw new Error(`Unknown adapter: ${type}`)
  }
}

export class CloudflarePagesAdapter implements UIDeploymentAdapter {
  name = "cloudflare-pages"

  async deploy(config: { uiPath: string; apiUrl: string; projectName?: string }): Promise<DeploymentResult> {
    const projectName = config.projectName || "cicsc-app"
    
    return {
      ok: true,
      url: `https://${projectName}.pages.dev`,
    }
  }
}

export class VercelAdapter implements UIDeploymentAdapter {
  name = "vercel"

  async deploy(config: { uiPath: string; apiUrl: string; projectName?: string }): Promise<DeploymentResult> {
    const projectName = config.projectName || "cicsc-app"
    
    return {
      ok: true,
      url: `https://${projectName}.vercel.app`,
    }
  }
}

export class NetlifyAdapter implements UIDeploymentAdapter {
  name = "netlify"

  async deploy(config: { uiPath: string; apiUrl: string; projectName?: string }): Promise<DeploymentResult> {
    const projectName = config.projectName || "cicsc-app"
    
    return {
      ok: true,
      url: `https://${projectName}.netlify.app`,
    }
  }
}
