package viper.silicon.reporting

import viper.silver.reporter.Statistics

object SolverStatistics {
  def apply(values: Map[String, String]): Z3Statistics = {
    Z3Statistics(values.getOrElse("rlimit-count", "0").toLong, values.getOrElse("quant-instantiations", "0").toLong)
  }
}

case class Z3Statistics(rlimitCount: Long, quantifierInstantiations: Long) extends Statistics {

  def subtract(other: Z3Statistics): Z3Statistics = {
    Z3Statistics(
      this.rlimitCount - other.rlimitCount,
      this.quantifierInstantiations - other.quantifierInstantiations
    )
  }

  def add(other: Z3Statistics): Z3Statistics = {
    Z3Statistics(
      this.rlimitCount + other.rlimitCount,
      this.quantifierInstantiations + other.quantifierInstantiations
    )
  }

  override def toString: String = {
    s"${this.rlimitCount},${this.quantifierInstantiations}"
  }
}
