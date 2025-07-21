/******************************************************************************
 * Top contributors (to current version):
 *   Andres Noetzli
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * IDL extension.
 */

#include "theory/arith/idl/idl_extension.h"

#include <iomanip>
#include <queue>
#include <set>

#include "expr/node_builder.h"
#include "theory/arith/theory_arith.h"
#include "theory/rewriter.h"
#include "theory/theory_model.h"
#include "util/rational.h"

namespace cvc5::internal {
namespace theory {
namespace arith {
namespace idl {

IdlExtension::IdlExtension(Env& env, TheoryArith& parent)
    : EnvObj(env),
      d_parent(parent),
      d_varMap(context()),
      d_varList(context()),
      d_facts(context()),
      d_numVars(0)
{
}

IdlExtension::~IdlExtension() {
}

void IdlExtension::preRegisterTerm(TNode node)
{
  Assert(d_numVars == 0);
  if (node.isVar())
  {
    Trace("theory::arith::idl")
        << "IdlExtension::preRegisterTerm(): processing var " << node
        << std::endl;
    unsigned size = d_varMap.size();
    d_varMap[node] = size;
    d_varList.push_back(node);
  }
}

void IdlExtension::presolve()
{
  d_numVars = d_varMap.size();
  Trace("theory::arith::idl")
      << "IdlExtension::preSolve(): d_numVars = " << d_numVars << std::endl;

  // Initialize adjacency matrix.
  for (size_t i = 0; i < d_numVars; ++i)
  {
    d_matrix.emplace_back(d_numVars);
    d_valid.emplace_back(d_numVars, false);
  }
}

void IdlExtension::notifyFact(
    TNode atom, bool pol, TNode fact, bool isPrereg, bool isInternal)
{
  Trace("theory::arith::idl")
      << "IdlExtension::notifyFact(): processing " << fact << std::endl;
  d_facts.push_back(fact);
}

Node IdlExtension::ppStaticRewrite(TNode atom)
{
  // We are only interested in predicates
  if (!atom.getType().isBoolean())
  {
    return atom;
  }

  Trace("theory::arith::idl")
      << "IdlExtension::ppStaticRewrite(): processing " << atom << std::endl;
  NodeManager* nm = NodeManager::currentNM();

  if (atom[0].getKind() == Kind::CONST_INTEGER)
  {
    // Move constant value to right-hand side
    Kind k = Kind::EQUAL;
    switch (atom.getKind())
    {
      // -------------------------------------------------------------------------
      // TODO: Handle these cases.
      // -------------------------------------------------------------------------
      case Kind::EQUAL: k = Kind::EQUAL; break;
      case Kind::LT:    k = Kind::GT;    break;
      case Kind::LEQ:   k = Kind::GEQ;   break;
      case Kind::GT:    k = Kind::LT;    break;
      case Kind::GEQ:   k = Kind::LEQ;   break;
      default: break;
    }
    return ppStaticRewrite(nm->mkNode(k, atom[1], atom[0]));
  }
  else if (atom[1].getKind() == Kind::VARIABLE)
  {
    // Handle the case where there are no constants, e.g., (= x y) where both
    // x and y are variables
    // -------------------------------------------------------------------------
    // TODO: Handle this case.
    // -------------------------------------------------------------------------
    // Handle the case where there are no constants, e.g., (= x y)
    Node diff = nm->mkNode(Kind::SUB, atom[0], atom[1]);  // x - y
    Node zero = nm->mkConstInt(0);                        // 0
    Node rewritten = nm->mkNode(atom.getKind(), diff, zero);  // (= (- x y) 0)
    return ppStaticRewrite(rewritten);  // Process this new form recursively
  }

  switch (atom.getKind())
  {
    case Kind::EQUAL:
    {
      Node l_le_r = nm->mkNode(Kind::LEQ, atom[0], atom[1]);
      Assert(atom[0].getKind() == Kind::SUB);
      Node negated_left = nm->mkNode(Kind::SUB, atom[0][1], atom[0][0]);
      const Rational& right = atom[1].getConst<Rational>();
      Node negated_right = nm->mkConstInt(-right);
      Node r_le_l = nm->mkNode(Kind::LEQ, negated_left, negated_right);
      return nm->mkNode(Kind::AND, l_le_r, r_le_l);
    }

    // -------------------------------------------------------------------------
    // TODO: Handle these cases.
    // -------------------------------------------------------------------------
    case Kind::LT:
    {
      // (x - y) < c  ⇨  (x - y) ≤ c - 1
      Assert(atom[1].getKind() == Kind::CONST_INTEGER);
      const Rational& c = atom[1].getConst<Rational>();
      Node c_minus_1 = nm->mkConstInt(c - 1);
      return nm->mkNode(Kind::LEQ, atom[0], c_minus_1);
    }
    case Kind::LEQ:
    {
        return atom;
    }
    case Kind::GT:
    {
      // (x - y) > c  ⇨  (y - x) ≤ -c - 1
      Assert(atom[1].getKind() == Kind::CONST_INTEGER);
      const Rational& c = atom[1].getConst<Rational>();
      Node flipped = nm->mkNode(Kind::SUB, atom[0][1], atom[0][0]);  // y - x
      Node newConst = nm->mkConstInt(-c - 1);                        // -c - 1
      return nm->mkNode(Kind::LEQ, flipped, newConst);              // (<= (- y x) -c -1)
    }
    case Kind::GEQ:
    {
      // (x - y) ≥ c  ⇨  (y - x) ≤ -c
      Assert(atom[1].getKind() == Kind::CONST_INTEGER);
      const Rational& c = atom[1].getConst<Rational>();
      Node flipped = nm->mkNode(Kind::SUB, atom[0][1], atom[0][0]);  // y - x
      Node newConst = nm->mkConstInt(-c);                            // -c
      return nm->mkNode(Kind::LEQ, flipped, newConst);              // (<= (- y x) -c)
    }
      // -------------------------------------------------------------------------

    default: break;
  }
  return atom;
}

void IdlExtension::postCheck(Theory::Effort level)
{
  if (!Theory::fullEffort(level))
  {
    return;
  }

  Trace("theory::arith::idl")
      << "IdlExtension::postCheck(): number of facts = " << d_facts.size()
      << std::endl;

  // Reset the graph
  for (size_t i = 0; i < d_numVars; i++)
  {
    for (size_t j = 0; j < d_numVars; j++)
    {
      d_valid[i][j] = false;
    }
  }

  for (Node fact : d_facts)
  {
    // For simplicity, we reprocess all the literals that have been asserted to
    // this theory solver. A better implementation would process facts in
    // notifyFact().
    Trace("theory::arith::idl")
        << "IdlExtension::check(): processing " << fact << std::endl;
    processAssertion(fact);
  }

  if (negativeCycle())
  {
    // Return a conflict that includes all the literals that have been asserted
    // to this theory solver. A better implementation would only include the
    // literals involved in the conflict here.
    NodeBuilder conjunction(Kind::AND);
    for (Node fact : d_facts)
    {
      conjunction << fact;
    }
    Node conflict = conjunction;
    // Send the conflict using the inference manager. Each conflict is assigned
    // an ID. Here, we use  ARITH_CONF_IDL_EXT, which indicates a generic
    // conflict detected by this extension
    d_parent.getInferenceManager().conflict(conflict,
                                            InferenceId::ARITH_CONF_IDL_EXT);
    return;
  }
}

bool IdlExtension::collectModelInfo(TheoryModel* m,
                                    const std::set<Node>& termSet)
{
  size_t n = d_numVars;
  NodeManager* nm = NodeManager::currentNM();

  // הוספת קודקוד מדומה שמחובר לכולם עם קשתות משקל 0
  std::vector<Rational> distance(n + 1, Rational(0));  // n is dummy node
  std::vector<std::pair<size_t, size_t>> edges;
  std::vector<Rational> weights;

  // יצירת רשימת הקשתות מהטבלה
  for (size_t u = 0; u < n; ++u)
  {
    for (size_t v = 0; v < n; ++v)
    {
      if (d_valid[u][v])
      {
        // זוכרים: x - y ≤ c ⇨ קשת מ־y ל־x במשקל c ⇒ קשת מ־v ל־u
        edges.emplace_back(v, u);
        weights.push_back(d_matrix[u][v]);
      }
    }
  }

  // הוספת קשתות מהקודקוד המדומה לכל משתנה במשקל 0
  for (size_t i = 0; i < n; ++i)
  {
    edges.emplace_back(n, i);  // dummy → i
    weights.push_back(Rational(0));
  }

  // Bellman-Ford: n+1 קודקודים, source = dummy (index n)
  for (size_t iter = 0; iter < n; ++iter)
  {
    bool updated = false;
    for (size_t i = 0; i < edges.size(); ++i)
    {
      size_t u = edges[i].first;
      size_t v = edges[i].second;
      Rational w = weights[i];
      if (distance[u] + w < distance[v])
      {
        distance[v] = distance[u] + w;
        updated = true;
      }
    }
    if (!updated) break;
  }

  // השמה למודל: x_i = distance[i]
  for (size_t i = 0; i < n; i++)
  {
    m->assertEquality(d_varList[i], nm->mkConstInt(distance[i]), true);
  }

  return true;
}


void IdlExtension::processAssertion(TNode assertion)
{
  bool polarity = assertion.getKind() != Kind::NOT;
  TNode atom = polarity ? assertion : assertion[0];
  Assert(atom.getKind() == Kind::LEQ);
  Assert(atom[0].getKind() == Kind::SUB);
  TNode var1 = atom[0][0];
  TNode var2 = atom[0][1];

  Rational value = (atom[1].getKind() == Kind::NEG)
                       ? -atom[1][0].getConst<Rational>()
                       : atom[1].getConst<Rational>();

  if (!polarity)
  {
    std::swap(var1, var2);
    value = -value - Rational(1);
  }

  size_t index1 = d_varMap[var1];
  size_t index2 = d_varMap[var2];

  if (!d_valid[index1][index2] || value < d_matrix[index1][index2])
  {
    d_valid[index1][index2] = true;
    d_matrix[index1][index2] = value;
  }
}

bool IdlExtension::negativeCycle()
{
  // --------------------------------------------------------------------------
  // TODO: write the code to detect a negative cycle.
  // --------------------------------------------------------------------------

  size_t n = d_matrix.size();
  // נבנה מטריצת מרחקים (נעתיק את השכנויות)
  std::vector<std::vector<Rational>> dist(n, std::vector<Rational>(n, Rational(INT_MAX / 2)));

  for (size_t i = 0; i < n; ++i)
  {
    for (size_t j = 0; j < n; ++j)
    {
      if (d_valid[i][j])
      {
        dist[i][j] = d_matrix[i][j];  // יש קשת מ־i ל־j
      }
    }
    dist[i][i] = 0;  // מרחק לעצמי הוא אפס
  }

  // אלגוריתם Floyd–Warshall
  for (size_t k = 0; k < n; ++k)
  {
    for (size_t i = 0; i < n; ++i)
    {
      for (size_t j = 0; j < n; ++j)
      {
        if (dist[i][k] + dist[k][j] < dist[i][j])
        {
          dist[i][j] = dist[i][k] + dist[k][j];
        }
      }
    }
  }

  // בדיקה למעגל שלילי
  for (size_t i = 0; i < n; ++i)
  {
    if (dist[i][i] < 0)
    {
      return true;
    }
  }

  return false;
}

void IdlExtension::printMatrix(const std::vector<std::vector<Rational>>& matrix,
                               const std::vector<std::vector<bool>>& valid)
{
  std::cout << "      ";
  for (size_t j = 0; j < d_numVars; ++j)
  {
    std::cout << std::setw(6) << d_varList[j];
  }
  std::cout << std::endl;
  for (size_t i = 0; i < d_numVars; ++i)
  {
    std::cout << std::setw(6) << d_varList[i];
    for (size_t j = 0; j < d_numVars; ++j)
    {
      if (valid[i][j])
      {
        std::cout << std::setw(6) << matrix[i][j];
      }
      else
      {
        std::cout << std::setw(6) << "oo";
      }
    }
    std::cout << std::endl;
  }
}

}  // namespace idl
}  // namespace arith
}  // namespace theory
}  // namespace cvc5