<?
  function php_to_js_array($n, $a) // no escape & co
  {
    $r = 'var ' . $n . ' = {';
    foreach ($a as $k => $v)
      $r .= "'$k': '$v',";
    $r .= '};';
    return $r;
  }

  function dir_tree($name, $prefix, $filter_ext)
  {
    $r = array( 'n' => '', 'f' => array(), 'd' => array() );
    $files = scandir($prefix . $name);
    foreach ($files as $f)
    {
      if ($f[0] == '.')
        continue;
      $loc = $name == '' ? $f : $name . '/' . $f;
      $full = $prefix . $loc;
      if (is_dir($full))
      {
        $r['d'][$f] = dir_tree($loc, $prefix, $filter_ext);
        $r['d'][$f]['n'] = $loc;
      }
      else if (isset($filter_ext[pathinfo($full, PATHINFO_EXTENSION)]))
        $r['f'][$f] = $loc;
    }
    return $r;
  }
?>
