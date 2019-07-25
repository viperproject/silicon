package viper.silicon.logger.renderer

trait Renderer[S, T] {
  def renderMember(s: S): T

  def render(memberList: List[S]): T
}
