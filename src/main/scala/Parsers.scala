
object Parsers {

  def lastChar(str: String): Char = str.charAt(str.length-1)

  implicit def string(str: String): Parser = if( str.isEmpty ) Epsilon else concat(literal(str.charAt(0)), string(str.substring(1)))

  implicit def literal(c: Char): Parser = ContainsParser(_==c)

  def range(min: Char, max: Char): Parser = ContainsParser(x=>min<=x && x<=max)

  def contains(fn: Char=>Boolean): Parser = ContainsParser(fn)

  def multiple(inner: Parser): Parser = concat(inner, kleene(inner))

  def optional(inner: Parser): Parser = union(Epsilon, inner)

  def union(parsers: Parser*): Parser = parsers.reduce[Parser](UnionParser(_,_ ))

  def capture(inner: Parser): Parser = CaptureParser(inner, None)

  def kleene(inner: Parser): Parser = inner match {
    case Epsilon => Epsilon
    case _ => KleeneParser(inner);
  }

  def concat(parsers: Parser*): Parser = parsers.reduce[Parser]({
    case (Epsilon, right) => right
    case (left, Epsilon) => left
    case (left, right) => ConcatParser(left, right)
  })


  private[Parsers] def combine(left: Evaluator, right: Evaluator): Evaluator = (left, right) match {
    case (Rejected, _) => right
    case (_, Rejected) => left
    case _ => Disjonction(left, right)
  }

  private[Parsers] def chain(evaluator: Evaluator, parser: Parser): Evaluator = evaluator match {
    case Rejected => Rejected
    case Disjonction(leftParser, rightParser) => combine(chain(leftParser, parser), chain(rightParser, parser))
    case Continuable(c @ CaptureParser(Epsilon, _), content, context) => Continuable(parser, content, context.flush())
    case Continuable(inner, content, context) => Continuable(concat(inner, parser), content, context)
  }

  private[Parsers] def capturing(evaluator: Evaluator, capture: CaptureParser): Evaluator = evaluator match {
    case Rejected => Rejected
    case Disjonction(leftParser, rightParser) => capturing(evaluator, capture)
    case Continuable(inner, content, context) => Continuable(CaptureParser(inner, Some(capture)), content, context)
  }


  sealed trait EvaluationContext {
    def flush(captures: List[String] = List()): EvaluationContext
    def capture(key: CaptureParser, content: String): EvaluationContext
    def continuable(parser: Parser, content: String, evaluationContext: EvaluationContext => EvaluationContext = identity[EvaluationContext]) : Evaluator
  }

  private[Parsers] case class EvaluationContextCapture(val next: EvaluationContext, key: CaptureParser, current: List[Char]) extends EvaluationContext {
    override def capture(key: CaptureParser, content: String) =
      if( this.key.key() == key.key() )
        EvaluationContextContinuable(next, this.key, lastChar(content) :: this.current)
      else
        EvaluationContextContinuable(this.flush(), key.key(), lastChar(content) :: Nil)
    override def flush(captures: List[String] = List()) =
      next.flush(current.reverse.mkString :: captures)
    override def continuable(parser: Parser, content: String, evaluationContext: EvaluationContext => EvaluationContext): Evaluator =
      this.flush().continuable(parser, content, evaluationContext)
  }

  private[Parsers] case class EvaluationContextContinuable(val next: EvaluationContext, key: CaptureParser, current: List[Char]) extends EvaluationContext {
    override def flush(captures: List[String]) =
      next.flush(captures)
    override def capture(key: CaptureParser, content: String): EvaluationContext =
      next.capture(key, content)
    override def continuable(parser: Parser, content: String, evaluationContext: EvaluationContext => EvaluationContext): Evaluator =
      next.continuable(parser, content, evaluationContext => new EvaluationContextCapture(evaluationContext, this.key, this.current))
  }

  private[Parsers] case class EvaluationContextProcess(val next: EvaluationContext, captured: List[String]) extends EvaluationContext {
    override def flush(captures: List[String]) =
      next.flush(captures ::: this.captured)
    override def capture(key: CaptureParser, content: String) =
      EvaluationContextContinuable(this, key, List(lastChar(content)))
    override def continuable(parser: Parser, content: String, evaluationContext: EvaluationContext => EvaluationContext): Evaluator =
      Continuable(parser, content, evaluationContext(this)) // next.continuable(parser, content, new EvaluationContextProcess(evaluationContext, this.captured))
  }

  private[Parsers] case object EvaluationEmpty extends EvaluationContext {
    override def capture(key: CaptureParser, content: String) =
      EvaluationContextContinuable(this, key, List(lastChar(content)))
    override def continuable(parser: Parser, content: String, evaluationContext: EvaluationContext=>EvaluationContext) =
      Continuable(parser, content, evaluationContext(this))
    override def flush(captures: List[String]) =
      EvaluationContextProcess(this, captures)
  }




  sealed trait Evaluator {
    def evaluate(str: String): Evaluator
    def result(orElse: =>Evaluator): Evaluator
  }
  case class Disjonction(left: Evaluator, right: Evaluator) extends Evaluator {
    def result(orElse: =>Evaluator) = left.result(right.result(orElse))
    def evaluate(str: String) = combine(left.evaluate(str), right.evaluate(str))
  }
  case class Continuable(parser: Parser, content: String, context: EvaluationContext) extends Evaluator {
    def evaluate(str: String) = parser.evaluate(str, context)
    def result(orElse: =>Evaluator) = if(parser.isNullable) this else orElse;
  }
  case object Rejected extends Evaluator {
    def evaluate(str: String) = Rejected
    def result(orElse: =>Evaluator) = orElse
  }




  sealed trait Parser {
    def isNullable: Boolean
    def evaluate(str: String, ctx: EvaluationContext): Evaluator

    def apply(str: Stream[Char], current: Evaluator = Continuable(this, "", EvaluationEmpty), processed: String = ""): Evaluator =
      if( str.isEmpty )
        current
      else {
        val next = current.evaluate(processed + str.head)
        apply(str.tail, next, processed + str.head)
      }
  }

  case object Epsilon extends Parser {
    val isNullable = true
    def evaluate(str: String, ctx: EvaluationContext) = Rejected
  }
  case object Any extends Parser {
    val isNullable = false;
    def evaluate(str: String, ctx: EvaluationContext) = ctx.continuable(Epsilon, str)
  }
  case class ContainsParser(fn: Char=>Boolean) extends Parser {
    override val isNullable = false;
    override def evaluate(str: String, ctx: EvaluationContext) = if(fn(lastChar(str))) ctx.continuable(Epsilon, str) else Rejected
  }
  case class KleeneParser(inner: Parser) extends Parser {
    override val isNullable: Boolean = true
    override def evaluate(str: String, ctx: EvaluationContext) = chain(inner.evaluate(str, ctx), this) // lazy eval
  }
  case class ConcatParser(left: Parser, right: Parser) extends Parser {
    override val isNullable = left.isNullable && right.isNullable
    override def evaluate(str: String, ctx: EvaluationContext) =
      if (left.isNullable)
        combine(chain(left.evaluate(str, ctx), right), right.evaluate(str, ctx))
      else
        chain(left.evaluate(str, ctx), right)
  }
  case class UnionParser(left: Parser, right: Parser) extends Parser {
    override val isNullable = left.isNullable || right.isNullable
    override def evaluate(str: String, ctx: EvaluationContext) = combine(left.evaluate(str, ctx), right.evaluate(str, ctx))
  }
  case class CaptureParser(inner: Parser, owner: Option[CaptureParser]) extends Parser {
    def key(): CaptureParser = owner.getOrElse(this)
    override def isNullable: Boolean = inner.isNullable
    override def evaluate(str: String, ctx: EvaluationContext) = capturing(inner.evaluate(str, ctx.capture(this, str)), owner.getOrElse(this))
  }











  val space: Parser = union(literal(0x20), literal(0x09), literal(0x0D), literal(0x0A))
  val spaces: Parser = multiple(space)
  val charCData = union(literal(0x9), literal(0xA), literal(0xD), range(0x20,0xD7FF), range(0xE000, 0xFFFD)/*, range(0x10000, 0x10FFFF)*/)
  val charText: Parser = union(range(0x01, 0x0D7FF), range(0x0E000, 0xFFFD)/*, range(0x10000, 0x10FFFF)*/)
  val charRestricted: Parser = union(range(0x1,0x8), range(0xB,0xC), range(0xE,0x1F), range(0x7F,0x84), range(0x86,0x9F))
  val charData: Parser = concat(
    kleene(concat(
      contains(x=>x!='<' && x!='&' && x!='"' && x!=']'),
      contains(x=>x!='<' && x!='&' && x!='"' && x!=']'),
      contains(x=>x!='<' && x!='&' && x!='"' && x!='>')
    )),
    optional(contains(x=>x!='<' && x!='&' && x!='"')),
    optional(contains(x=>x!='<' && x!='&' && x!='"'))
  )

  val hexadecimal = multiple(
    union(range('0', '9'), range('a', 'f'), range('A', 'F'))
  )
  val decimal = multiple(
    range('0', '9')
  )

  val nameStartChar: Parser = union(
    literal(':'), literal('_'), range('A', 'Z'), range('a', 'z'),
    range(0xC0,0xD6), range(0xD8,0x0F6), range(0xF8, 0x2FF), range(0x370,0x37D),
    range(0x37F,0x1FFF), range(0x200C, 0x200D), range(0x2070,0x218F), range(0x2C00, 0x2FEF),
    range(0x3001,0xD7FF), range(0xF900,0xFDCF), range(0xFDF0,0xFFFD)
  )
  val nameChar: Parser = union(nameStartChar, literal('-'), literal('.'), range('0','9'), literal(0x0B7), range(0x0300, 0x036F), range(0x203F, 0x2040) )
  val name: Parser = concat(nameStartChar, kleene(nameChar))
  val names: Parser = concat(name, kleene(concat(' ', name)))

  val nmToken: Parser = multiple(nameChar)
  val nmTokens: Parser = concat(nmToken, kleene(concat(' ', nmToken)))


  val reference: Parser = concat('&', union(name, concat("#", decimal), concat("#x", hexadecimal)), ';')
  val comment: Parser = concat("<!--", kleene(union(contains(_!='-'), concat('-', contains(_!='-')))), "-->")
  val cdata: Parser = concat("<![CDATA[", kleene(union(contains(_!=']'), concat(']', union(contains(_!=']'), concat(']', contains(_!='>')))) )), "]]>")
  val processingInstruction: Parser = concat('<', '?', name, optional(concat(multiple(space), name)), '?', '>')
  val attributeChars: Parser = contains(x=>x!='<' && x!='&' && x!='"');
  val elementStart: Parser = concat('<', capture(name), kleene(concat(multiple(space), capture(name), '=', '"', capture(kleene(union(attributeChars, reference))), '"')), kleene(space), union("/>", ">"));
  val elementEnd: Parser = concat('<', '/', name, '>')


  val test1: Parser = concat('<', capture(kleene(range('a','z'))), '>')
  val test2: Parser = concat('<', kleene(capture(range('a','z'))), '>')
  val test3: Parser = concat('<', kleene(concat(capture(range('a', 'z')), '=', capture(kleene(union(range('1', '4'), range('6', '9')))), union(' ', Epsilon))), '>')

  def main(args: Array[String]): Unit = {

    // gc();
    val startTime = System.currentTimeMillis();
    val startMemory = (Runtime.getRuntime().totalMemory() -  Runtime.getRuntime().freeMemory())
    // val result = elementStart("<a>zut".toStream)
    val result = elementStart("<elementName attrKey1=\"attrValue1\" attrKey2=\"attrValue2&lt;\"/>".toStream)
    // val result = elementStart("<elementName attrKey1=\"attrValue1\" attrKey2=\"attrVal".toStream)
    // val result = comment("<!-- B+, B, or B--->".toStream)
    // val result = comment("<!-- declarations for <head> & <body> -->".toStream)
    // val result = cdata("<![CDATA[<greeting>Hello, world!</greeting>]]>".toStream)
    // val result = test2("<abcd>".toStream)
    // val result = test3("<a=1 b=2>".toStream)
    println("")
    println(result)

    val endTime = System.currentTimeMillis();
    // gc()
    val endMemory = (Runtime.getRuntime().totalMemory() -  Runtime.getRuntime().freeMemory())
    println(s"time= ${endTime - startTime} - memory=${(endMemory - startMemory) / 1024d}")
  }

  def gc() {
    val  ref = new java.lang.ref.WeakReference(new  java.lang.ref.WeakReference(Array.fill(1024*1034*256)(0)));
    while(ref.get() != null) {
      System.gc();
    }
  }
}