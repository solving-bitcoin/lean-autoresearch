import Blake3Prize.Submission.RomBytes

/-! Four-row binary and two-row output translation tables. Semantic row bits
are known to the evaluator; external labels have no imposed selector bit.
The context will identify the gate and row in the circuit serialization. -/
namespace Blake3Prize.Submission.RomGate
open SecretRelease

abbrev Row := Bool × Bool

def query (context : ByteArray) (left right : Label) : ByteArray :=
  context ++ RomBytes.encode left ++ RomBytes.encode right

def table (hash : Hash) (context : Row → ByteArray)
    (function : Bool → Bool → Bool) (left right output : Bool → Label) : Row → Label :=
  fun row => RomBytes.xor (output (function row.1 row.2))
    (hash (query (context row) (left row.1) (right row.2)))

def evaluate (hash : Hash) (context : ByteArray) (ciphertext left right : Label) : Label :=
  RomBytes.xor ciphertext (hash (query context left right))

theorem evaluate_table (hash : Hash) (context : Row → ByteArray)
    (function : Bool → Bool → Bool) (left right output : Bool → Label) (a b : Bool) :
    evaluate hash (context (a,b)) (table hash context function left right output (a,b))
      (left a) (right b) = output (function a b) :=
  RomBytes.xor_cancel_right _ _

def translate (hash : Hash) (context : Bool → ByteArray) (source output : Bool → Label) : Bool → Label :=
  fun bit => RomBytes.xor (output bit)
    (hash (context bit ++ RomBytes.encode (source bit)))

def openTranslation (hash : Hash) (context : ByteArray) (ciphertext key : Label) : Label :=
  RomBytes.xor ciphertext (hash (context ++ RomBytes.encode key))

theorem openTranslation_translate (hash : Hash) (context : Bool → ByteArray)
    (source output : Bool → Label) (bit : Bool) :
    openTranslation hash (context bit) (translate hash context source output bit)
      (source bit) = output bit :=
  RomBytes.xor_cancel_right _ _

end Blake3Prize.Submission.RomGate
