class SATSolver
  def initialize
    @cnt = 0
    @ok = true
    @clauses = []
    @model = Hash.new
    @watches = Hash.new
  end

  def new_var
    @cnt += 1
    @cnt
  end

  def <<(clause)
    return false unless @ok
    clause = [clause] if Integer === clause

    case clause.size
    when 0
      @ok = false
      false
    when 1
      set(clause[0])
    else
      w1 = w2 = nil

      clause.each{|lit|
        v = lit.abs
        if @model.key? v          
          return true if self[lit]
        else
          if w1.nil?
            w1 = lit
          elsif w2.nil?
            w2 = lit
          end
        end
      }

      if w1.nil? && w2.nil?
        conflict
      elsif w2.nil?
        set(w1.literal)
      else
        c = Clause.new(clause, nil, nil)
        c.w1 = add_watch(c, w1)
        c.w2 = add_watch(c, w2)
        @clauses.push c
      end
    end
  end

  def solve
    @ok and solve1(1)
  end

  def [](lit)
    var = lit.abs
    val = @model[var]
    if lit < 0 && !val.nil?
      val = !val
    end
    val 
  end

  def ok?
    @ok
  end

  attr_reader :model

  private

  def solve1(v)
    return true if v > @cnt
    
    if @model.key? v
      solve1(v+1)
    else
      m = @model
      @model = m.dup
      (@model = m.dup and set(v) and solve1(v+1)) or
        (@model = m.dup and set(-v) and solve1(v+1))
    end
  end

  def add_watch(clause, lit)
    v = lit.abs
    w = Watch.new(clause, lit)
    (@watches[v] ||= []).push(w)
    w
  end

  def set(lit)
    var = lit.abs
    val = (lit > 0)

    if @model.key? var && @model[var] != val
      return conflict
    end

    @model[var] = val

    ws = @watches[var]
    return true if ws.nil?

    while !ws.empty?
      w = ws.last

      c = w.clause

      w2 = (if c.w1.equal? w then c.w2 else c.w1 end)
      w2_lit = w2.literal

      lit = nil
      sat = false
      c.literals.each{|l|
        v = l.abs
        if @model.key? v
          if self[l]
            sat = true
            break
          end
        elsif l != w2_lit
          lit = l
          break
        end
      }

      unless sat
        if lit
          v = lit.abs
          w.literal = lit
          (@watches[v] ||= []).push(w)
        else
          set(w2_lit)
        end
      end
      
      ws.pop
    end

    true
  end

  def conflict
    @ok = false
    false
  end

  Clause = Struct.new(:literals, :w1, :w2)
  Watch = Struct.new(:clause, :literal)
end


if __FILE__ == $0
  solver = SATSolver.new
  p = solver.new_var
  q = solver.new_var
  r = solver.new_var
  solver << [p, q, -r]
  solver << [-q, p]
  solver << -p
  solver << [r, p]
  p solver.solve #=> false
  
  solver = SATSolver.new
  s = solver.new_var
  t = solver.new_var
  p = solver.new_var
  u = solver.new_var
  solver << [s, t]
  solver << [-s, -t]
  solver << [p, u]
  solver << [-p, u]
  p solver.solve #=> true
  p solver.model #=> {1=>true, 2=>false, 3=>true, 4=>true}
end
