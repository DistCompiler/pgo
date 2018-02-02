package pgonet

// Implements the state ownership strategy.

type OwnershipStateDistribution struct {
}

func NewWithConfig(c *Config) *OwnershipStateDistribution {
	return &OwnershipStateDistribution{}
}
