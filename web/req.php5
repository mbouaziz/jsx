<?
error_reporting(-1);
  require_once 'config.php5';
  require_once 'lang_options.php5';
  require_once 'env_options.php5';
  require_once 'bool_options.php5';
  require_once 'jsx.php5';

  function request_string($id)
  {
    return isset($_REQUEST[$id]) ? stripslashes($_REQUEST[$id]) : '';
  }

  function request_bool($id, $def = false)
  {
    return isset($_REQUEST[$id]) ? (bool)$_REQUEST[$id] : $def;
  }

  function request_var_in_array($id, $arr, $def)
  {
    if (!isset($_REQUEST[$id]))
      return $def;
    $v = $_REQUEST[$id];
    if (isset($arr[$v]))
      return $v;
    return $def;
  }
  
  function request_bool_array($id, $arr)
  {
    $r = array();
    foreach ($arr as $k => $v)
      $r[$k] = isset($_REQUEST[$id][$k]) ? (bool)$_REQUEST[$id][$k] : false;
    return $r;
  }

  $jsx_src = request_string('jsx_src');
  $firstlang = each($langlist);
  $jsx_lang = request_var_in_array('jsx_lang', $langlist, $firstlang[0]);
  $jsx_env = request_bool_array('jsx_env', $envlist);
  $jsx_opt = request_bool_array('jsx_opt', $boolspeclist);
  
  echo jsx($jsx_src, $jsx_lang, $jsx_env, $jsx_opt);
?>
