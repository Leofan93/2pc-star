/*
 *
 *
 * This copyrighted material is made available to anyone wishing to use, modify,
 * copy, or redistribute it subject to the terms and conditions of the GNU
 * Lesser General Public License, as published by the Free Software Foundation.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
 * or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU Lesser General Public License
 * for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with this distribution; if not, see <http://www.gnu.org/licenses/>.
 *
 */

package org.dromara.raincat.dubbo.interceptor;

import org.dromara.raincat.core.interceptor.AbstractTxTransactionAspect;
import org.aspectj.lang.annotation.Aspect;
import org.springframework.beans.factory.annotation.Autowired;
import org.springframework.core.Ordered;
import org.springframework.stereotype.Component;

/**
 * DubboTxTransactionAspect.
 * @author xiaoyu
 */
@Aspect
@Component
public class DubboTxTransactionAspect extends AbstractTxTransactionAspect implements Ordered {

    @Autowired
    public DubboTxTransactionAspect(final DubboTxTransactionInterceptor dubboTxTransactionInterceptor) {
        this.setTxTransactionInterceptor(dubboTxTransactionInterceptor);
    }

    @Override
    public int getOrder() {
        return Ordered.HIGHEST_PRECEDENCE;
    }
}
