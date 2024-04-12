import React from 'react';
import { Tooltip, Typography, useTheme } from '@mui/material';
import { HEIGHT } from '../../constants/appointment';
import { useSchedulerContext } from '../../context/SchedulerProvider';
import { darken, styled } from '@mui/system';

const Text = styled(Typography)((props) => {
  return {
    '-webkit-box-orient': 'vertical',
    '-webkit-line-clamp': props.lines || 1,
    display: '-webkit-box',
    overflow: 'hidden',
    whiteSpace: 'nowrap',
    textOverflow: 'ellipsis',
    color: darken(props.color, 0.5),
    marginRight: 4,
    ...props.style,
  };
});

const Truncated = (props) => {
  const {
    text,
    tooltipMessage = '',
    tooltip,
    TooltipProps = {},
  } = props;
  return (
    <Tooltip title={tooltipMessage || tooltip} {...TooltipProps}>
      <Text {...props} >{text}</Text>
    </Tooltip>
  );
};

export default Truncated;
