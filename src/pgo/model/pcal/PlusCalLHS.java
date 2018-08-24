package pgo.model.pcal;

import pgo.model.tla.*;
import pgo.util.SourceLocation;

import java.util.Collections;
import java.util.List;
import java.util.Objects;
import java.util.stream.Collectors;

public class PlusCalLHS extends PlusCalNode {

	private final TLAIdentifier id;
	private final List<PlusCalLHSPart> parts;

	public PlusCalLHS(SourceLocation location, TLAIdentifier id, List<PlusCalLHSPart> parts) {
		super(location);
		this.id = id;
		this.parts = parts;
	}

	public TLAIdentifier getId() { return id; }
	public List<PlusCalLHSPart> getParts() { return parts; }

	public TLAExpression toExpression() {
		TLAExpression lhs = new TLAGeneralIdentifier(id.getLocation(), id, Collections.emptyList());
		for(PlusCalLHSPart part : parts) {
			switch(part.getType()) {
				case INDEX:
					lhs = new TLAFunctionCall(part.getLocation(), lhs, part.getArguments());
					break;
				case DOT:
					lhs = new TLABinOp(
							part.getLocation(),
							new TLASymbol(part.getLocation(), "."),
							Collections.emptyList(),
							lhs,
							new TLAGeneralIdentifier(
									part.getId().getLocation(),
									part.getId(),
									Collections.emptyList()));
					break;
			}
		}
		return lhs;
	}

	@Override
	public PlusCalLHS copy() {
		return new PlusCalLHS(
				getLocation(),
				id.copy(),
				parts.stream().map(PlusCalLHSPart::copy).collect(Collectors.toList()));
	}

	@Override
	public boolean equals(Object o) {
		if (this == o) return true;
		if (o == null || getClass() != o.getClass()) return false;
		PlusCalLHS that = (PlusCalLHS) o;
		return Objects.equals(id, that.id) &&
				Objects.equals(parts, that.parts);
	}

	@Override
	public int hashCode() {
		return Objects.hash(id, parts);
	}

	@Override
	public <T, E extends Throwable> T accept(PlusCalNodeVisitor<T, E> v) throws E {
		return v.visit(this);
	}
}
